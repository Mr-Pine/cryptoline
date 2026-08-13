#!/usr/bin/env python3
#
# This script utilizes python-enabled gdb on your $PATH to collect
# per-instruction execution trace for first invocation of named
# function [and its descendants]. It also annotates instructions
# that reference memory [as well as "lea"] with actual effective
# addresses and the memory segment each address falls in [".bss",
# "[stack]", ...]. Values read from ".rodata" are moved into the trace
# as constants unless --no-rodata-values says otherwise... It's even
# possible to "cross-trace" emulated target,
# e.g.:
#
#   qemu-arm -g 1234 a.out &
#   itrace.py a.out function :1234
#
# Alternatively if qemu-user-binfmt is configured, one can
#
#   env QEMU_GDB=1234 ./a.out &
#   itrace.py a.out function :1234
#
#                                           @dot-asm

import os
import sys
import re

debug_flag = False
#debug_flag = True

##############################################################################
# detect if already in gdb context, and if not, run gdb

try:
    gdb             # gdb module is pre-loaded in gdb context
except NameError:
    if len(sys.argv) < 3 or not os.access(sys.argv[1], os.X_OK):
        print("Usage: {0:s} executable function [remote-target] [output] [--error-conditional-branches | --unsound-warn-conditional-branches] [--no-rodata-values] [--stop-at SYM[,SYM...]] [-- args]".format(sys.argv[0]))
        sys.exit(-1)

    prog = [sys.argv[1]]

    # pass arguments through environment
    os.environ["TRACE_FUNCTION"] = sys.argv[2]
    os.environ["ITRACE_SCRIPT_DIR"] = os.path.dirname(os.path.abspath(sys.argv[0]))
    argv = sys.argv[3:]
    # what a conditional branch does: record its condition (the default),
    # stop with an error, or only warn
    if "--error-conditional-branches" in argv:
        argv.remove("--error-conditional-branches")
        os.environ["TRACE_BRANCH_POLICY"] = "error"
    if "--unsound-warn-conditional-branches" in argv:
        argv.remove("--unsound-warn-conditional-branches")
        os.environ["TRACE_BRANCH_POLICY"] = "warn"
    if "--no-rodata-values" in argv:
        argv.remove("--no-rodata-values")
        os.environ["TRACE_NO_RODATA_VALUES"] = "1"
    # functions to treat as opaque: run them, but record the call rather
    # than their instructions, for a proof that composes their contract
    if "--stop-at" in argv:
        i = argv.index("--stop-at")
        if i + 1 >= len(argv) or argv[i+1].startswith("-"):
            print("--stop-at needs a comma-separated list of symbols",
                  file=sys.stderr)
            sys.exit(-1)
        os.environ["TRACE_STOP_AT"] = argv[i+1]
        del argv[i:i+2]
    if len(argv) > 0 and re.match(r'/dev/|:', argv[0]):
        os.environ["TRACE_TARGET_REMOTE"] = argv.pop(0)
    if len(argv) > 0 and argv[0] != "--":
        os.environ["TRACE_OUTFILE"] = argv.pop(0)
    # pass remaining arguments on gdb command line
    if len(argv) > 1 and argv[0] == "--":
        prog.extend(argv[1:])

    try:
        os.execlpe("gdb-multiarch", "gdb", "--batch", "--nx",
                                    "--command=" + sys.argv[0],
                                    "--args", *prog,
                   os.environ)
    except OSError as e :
        if e.errno == 2 :    # no such file or directory, retry just gdb
            try:
                os.execlpe("gdb", "gdb", "--batch", "--nx",
                                  "--command=" + sys.argv[0],
                                  "--args", *prog,
                           os.environ)
            except OSError as e :
                pass
        sys.exit(e.errno)
    sys.exit(-1)

##############################################################################
# this part is executed in gdb context and that's where it all happens...

sys.path.insert(0, os.environ["ITRACE_SCRIPT_DIR"])
from itrace_arch import X86_64, ARM64, ARM32, MIPS, RISCV, \
                        ea_annotation, label, segment, BranchKind

function = os.environ["TRACE_FUNCTION"]
ea_only = "TRACE_EAONLY" in os.environ
branch_policy = os.environ.get("TRACE_BRANCH_POLICY", "record")
rodata_values = "TRACE_NO_RODATA_VALUES" not in os.environ
stop_at = set(filter(None, os.environ.get("TRACE_STOP_AT", "").split(",")))

# the trace is written to 'out' rather than to sys.stdout, so that gdb
# plugins loaded from the user's gdbinit can't leak their own output
# into it (see the comment on Extractor.__init__)
if "TRACE_OUTFILE" in os.environ:
    out = open(os.environ["TRACE_OUTFILE"], "w")
else:
    out = sys.stdout

# figure out if platform is 32- or 64-bit and instantiate extractor,
# all based on 'info target'...

target = gdb.execute("info target",to_string=True)
platform=re.search(r'file type (\w+)-([\w\-]+)',target)
elf=platform.group(1)
mach=platform.group(2);

if re.search(r'32$',elf):
    wordsize = 32
else:
    wordsize = 64

if re.search(r'x86-64',mach):
    # the extractor's operand patterns are AT&T syntax, so don't let a
    # gdbinit that prefers Intel syntax (pwndbg does) silently disable
    # all effective-address annotation
    gdb.execute("set disassembly-flavor att", to_string=True)
    extr = X86_64(64, out)
elif re.search(r'aarch64',mach):
    extr = ARM64(64, out)
elif re.search(r'arm',mach):
    extr = ARM32(32, out)
elif re.search(r'mips',mach):
    extr = MIPS(wordsize, out)
elif re.search(r'riscv',mach):
    extr = RISCV(wordsize, out)
else:
    raise Exception("Unsupported machine type: %s" % mach)

def debug(msg):
    if debug_flag:
        print("DEBUG: {}".format(msg))

# the count and the unit size of a load, as the extractors spell it for
# gdb's "x" command, e.g. "4xg"
loadpattern = re.compile(r'(\d+)x([bhwg])')
loadwidths = {"b": 8, "h": 16, "w": 32, "g": 64}

rodata_rules = set()        # widths a translation rule was emitted for
rodata_known = {}           # values already moved into the trace, by address

def isRodata(name):
    # ".rodata", but also ".rodata.cst8" and a shared library's "lib.so:.rodata"
    return name.split(":")[-1].startswith(".rodata")

def print_rodata_values(args, addr, fmt, values):
    # Move what the next instruction reads from .rodata into the trace, so
    # that it is a constant there rather than an unconstrained input. Nothing
    # stops a program from writing to .rodata, hence the warning.
    load = loadpattern.match(fmt)
    if not load or not all(v.startswith("0x") for v in values):
        return
    width = loadwidths[load.group(2)]
    for i, value in enumerate(values):
        address = addr + i * width // 8
        if rodata_known.get(address) == value:
            continue
        if not rodata_known:
            print("# WARNING: moving values read from .rodata into the trace, "
                  "which assumes that section really is constant; pass "
                  "--no-rodata-values to treat them as inputs instead",
                  file=sys.stderr)
        rodata_known[address] = value
        if width not in rodata_rules:
            rodata_rules.add(width)
            print("#! rodata_mov{0:d} $1c, $2v -> mov $2v $1c@uint{0:d}"
                  .format(width), file=out)
        insn = "rodata_mov{0:d} {1:s},%%{2:s}".format(width, value,
                                                      label(args, address))
        print("\t{0:48s} # .rodata at 0x{1:x}".format(insn, address), file=out)

stopped = []                # one callee name per call left untraced

# gdb annotates a branch target with the symbol it resolves to, e.g.
# "call 0x55555555a2e0 <fd_r43x6_is_nonzero>".  Ask the operand rather than
# the frame we land in: at the callee's first instruction gdb may already
# report an *inlined* frame from inside it (the AVX-512 intrinsic wrappers
# all show up that way), so frame.name() answers a different question than
# "who is being called".  A "+offset" target is a jump into the middle of a
# function, not a call to it, and deliberately does not match.
calltarget = re.compile(r'<([^+>]+)>\s*$')

def call_target_name(insn):
    m = calltarget.search(insn["asm"])
    return m.group(1) if m else None

def stop_at_call(name, retaddr):
    # A --stop-at callee: let it run, but record the call instead of its
    # instructions.  Its body is meant to be proven once, standalone,
    # against a contract that the caller's proof invokes -- so what the
    # caller's trace needs is that the call happened and to whom, not what
    # it did.  Whatever it wrote is the contract's business: CryptoLine's
    # `inlinespec' asserts the callee's precondition, makes the actual
    # outputs and everything the callee writes nondet, and assumes only its
    # postcondition, so omitting the body here cannot smuggle in an
    # assumption the contract does not state.
    #
    # `inlinespec' rather than `call': a call passes its inputs by value and
    # gives the callee a namespace of its own, which is not how a call works
    # here -- the callee shares the register file, so a register it clobbers
    # has to become nondet in the caller, under the name the caller knows it
    # by.  `inlinespec' substitutes the actuals for the formals and nondets
    # what the callee writes, so it models that; `call' does not.  Nor can
    # `inline' serve: there is no body to inline, which is the point of
    # stopping here.
    #
    # Run to the instruction after the call rather than `finish'ing the
    # frame: at the callee's first instruction gdb may already be showing
    # an inlined frame from inside it, and finishing *that* returns into
    # the middle of the callee, which silently traces the body this is
    # meant to skip.  The return address is not a guess -- it is the second
    # instruction of the disassembly the loop already fetched.
    # A plain `#' comment, not `#!': the latter introduces a translation
    # spec, and this is a note to whatever reads the trace, not a rule.  It
    # deliberately does not carry SP -- the caller's proof names the
    # callee's arguments by the ABI registers it already sees, and a marker
    # that looked like the `#! -> SP =' frame markers would be read as one.
    stopped.append(name)
    print("\t# stop-at {0:s} -- body not traced, prove it separately and "
          "compose its contract with inlinespec {0:s}".format(name), file=out)
    # ...and don't let the traced function's own breakpoint catch a
    # recursive call on the way through
    gdb.execute("disable breakpoints", to_string=True)
    gdb.execute("tbreak *0x{0:x}".format(retaddr), to_string=True)
    gdb.execute("continue", to_string=True)
    gdb.execute("enable breakpoints", to_string=True)
    if int(gdb.newest_frame().pc()) != retaddr:
        print("ERROR: stopping at {0:s} did not come back to 0x{1:x}"
              .format(name, retaddr), file=sys.stderr)
        out.flush()
        sys.exit(1)

conditions = []             # one condition name per conditional branch recorded

def print_conditional_branch(insn, addr):
    # The traced path stands for the whole function only where the branch
    # could not have gone the other way, so leave that obligation in the
    # trace for a translation rule to define and CryptoLine to prove.
    condition = extr.condition(insn)
    if not conditions:
        print("# WARNING: recording the condition of every conditional branch, "
              "which the translation has to define and CryptoLine to prove; "
              "pass --error-conditional-branches to stop at one instead",
              file=sys.stderr)
    conditions.append(condition)
    print("\t{0:48s} # conditional branch at 0x{1:x}"
          .format("conditional_branch " + condition, addr), file=out)

def trace():
    frame = gdb.newest_frame()
    arch = frame.architecture()

    print("\t#! -> SP = 0x{0:x}".format(int(frame.read_register("sp"))), file=out)
    while(frame.is_valid()):
        insns = arch.disassemble(frame.pc(), count=2)	# 2nd for delay slot
        mnemonic = extr.mnemonic(insns[0])
        debug("mnemonic = %s" % mnemonic)
        b = extr.isBranch(insns, frame)
        if b:                               # skip over flow control
            kind = extr.branch_kind(insns, b)
            if kind == BranchKind.CONDITIONAL:
                if branch_policy == "error":
                    print("ERROR: conditional branch at 0x{0:x}: {1:s} -- traced "
                          "path is not guaranteed to represent all inputs; drop "
                          "--error-conditional-branches to record its condition "
                          "instead"
                          .format(int(frame.pc()), mnemonic), file=sys.stderr)
                    out.flush()
                    sys.exit(1)
                elif branch_policy == "warn":
                    print("# WARNING: conditional branch at 0x{0:x}: {1:s} -- "
                          "traced path is not guaranteed to represent all inputs"
                          .format(int(frame.pc()), mnemonic), file=sys.stderr)
                else:
                    print_conditional_branch(insns[0], int(frame.pc()))
            if kind == BranchKind.RETURN:
                print("\t#! <- SP = 0x{0:x}".format(int(frame.read_register("sp"))), file=out)
            # resolve before stepping: afterwards this instruction is gone
            callee = retaddr = None
            if kind == BranchKind.CALL:
                callee = call_target_name(insns[0])
                retaddr = int(insns[1]["addr"])
            gdb.execute("stepi", to_string=True)
            debug("After stepi 1")
            print("\t#{:s}".format(mnemonic), file=out)
            if kind == BranchKind.CALL:     # calls are handled recursively
                debug("Call")
                if callee in stop_at:
                    stop_at_call(callee, retaddr)
                    frame = gdb.newest_frame()
                    arch = frame.architecture()
                else:
                    trace()
            elif kind == BranchKind.RETURN:
                debug("Return")
                return
            elif not frame.is_valid():      # inter-procedure branches
                debug("Invalid")
                frame = gdb.newest_frame()
                arch = frame.architecture()
            else:
                debug("Unhandled case")
        else:
            ea = extr.getEA(insns[0], frame)
            if ea :
                annotation = ea_annotation(extr.args, ea["addr"])
                if ea.get("load") and not ea_only :
                    values = []
                    try :
                        value = gdb.execute("x/{0} 0x{1:x}".format(ea["load"], ea["addr"]), False, True)
                        values.extend(re.findall(r'(0[xX][0-9a-fA-F]+\b)(?!(?:\s+<.*>)?:)', value))
                    except gdb.MemoryError :
                        values.append("'?'")
                    if rodata_values and isRodata(segment(ea["addr"])) :
                        print_rodata_values(extr.args, ea["addr"], ea["load"], values)
                    annotation += "; Value = {0}".format(" ".join(values))
                print("\t{0:48s}#! {1:s}".format(mnemonic, annotation), file=out)
            else:
                print("\t{0:s}".format(mnemonic), file=out)
            gdb.execute("stepi", to_string=True)
            debug("After stepi 2")
        if not frame.is_valid():      # inter-procedure branches
            debug("Unexpected invalid frame! Well, not necessarily...")
            frame = gdb.newest_frame()
            arch = frame.architecture()
        extr.archUpdate(mnemonic, frame)

    gdb.execute("stepi", to_string=True)    # step over retq
    debug("After stepi 3")
    return

# "main"

# quirk: even though gdb.Breakpoint is documented to have pending attribute
# it didn't work for me :-(
s = gdb.execute("break *" + function, to_string=True)
if re.search("not defined", s):             # symbol was not found
    print(s.split("\n")[0], file=sys.stderr)
    sys.exit(-1)

# bypass processor capbility detection
gdb.execute("handle SIGILL nostop", to_string=True)

# quirk: Without this, gdb tries to print a value that is null,
# failing an assertion. Since we don't need that value,
# we can ignore this.
gdb.execute("set print frame-arguments none", to_string=True)

if "TRACE_TARGET_REMOTE" in os.environ:
    gdb.execute("target remote " + os.environ["TRACE_TARGET_REMOTE"],
                to_string=True)
    gdb.execute("continue", to_string=True)
else :
    gdb.execute("run", to_string=True)

debug("After run")

# if the breakpoint was never hit the program just ran to completion and
# there is no live inferior left to trace, in which case every subsequent
# gdb command fails with a rather cryptic complaint about the 'exec'
# target...
if not gdb.selected_inferior().threads():
    print("ERROR: '{0:s}' was never reached, the program exited without "
          "hitting the breakpoint -- make sure it is the symbol actually "
          "executed by this run".format(function), file=sys.stderr)
    sys.exit(1)

gdb.execute("set scheduler-locking on", to_string=True)

extr.printHeader(function)
trace()
out.flush()

if rodata_known:
    print("# WARNING: {0:d} .rodata location(s) were moved into the trace"
          .format(len(rodata_known)), file=sys.stderr)

if conditions:
    print("# WARNING: {0:d} conditional branch(es) were recorded, each needing "
          "a translation rule for: {1:s}"
          .format(len(conditions), ", ".join(sorted(set(conditions)))),
          file=sys.stderr)

# say which --stop-at symbols never came up: asking to stop at a symbol that
# is never called (a typo, or one the compiler inlined after all) otherwise
# looks exactly like a trace that composed it, and silently proves less
if stop_at:
    print("# {0:d} call(s) left untraced: {1:s}"
          .format(len(stopped), ", ".join(sorted(set(stopped)))),
          file=sys.stderr)
    unused = stop_at - set(stopped)
    if unused:
        print("# WARNING: --stop-at named {0:s}, which was never called -- "
              "check the spelling, and that it was not inlined away"
              .format(", ".join(sorted(unused))), file=sys.stderr)

gdb.execute("delete breakpoints", to_string=True)
