#!/usr/bin/env python3
#
# This script utilizes python-enabled gdb on your $PATH to collect
# per-instruction execution trace for first invocation of named
# function [and its descendants]. It also annotates instructions
# that reference memory [as well as "lea"] with actual effective
# addresses... It's even possible to "cross-trace" emulated target,
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
        print("Usage: {0:s} executable function [remote-target] [output] [--warn-conditional-branches] [-- args]".format(sys.argv[0]))
        sys.exit(-1)

    prog = [sys.argv[1]]

    # pass arguments through environment
    os.environ["TRACE_FUNCTION"] = sys.argv[2]
    os.environ["ITRACE_SCRIPT_DIR"] = os.path.dirname(os.path.abspath(sys.argv[0]))
    argv = sys.argv[3:]
    if "--warn-conditional-branches" in argv:
        argv.remove("--warn-conditional-branches")
        os.environ["TRACE_WARN_BRANCHES"] = "1"
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
from itrace_arch import X86_64, ARM64, ARM32, MIPS, RISCV, label, BranchKind

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
    extr = X86_64(64)
elif re.search(r'aarch64',mach):
    extr = ARM64(64)
elif re.search(r'arm',mach):
    extr = ARM32(32)
elif re.search(r'mips',mach):
    extr = MIPS(wordsize)
elif re.search(r'riscv',mach):
    extr = RISCV(wordsize)
else:
    raise Exception("Unsupported machine type: %s" % mach)

def debug(msg):
    if debug_flag:
        print("DEBUG: {}".format(msg))

def trace():
    frame = gdb.newest_frame()
    arch = frame.architecture()

    print("\t#! -> SP = 0x{0:x}".format(int(frame.read_register("sp"))))
    while(frame.is_valid()):
        insns = arch.disassemble(frame.pc(), count=2)	# 2nd for delay slot
        mnemonic = extr.mnemonic(insns[0])
        debug("mnemonic = %s" % mnemonic)
        b = extr.isBranch(insns, frame)
        if b:                               # skip over flow control
            kind = extr.branch_kind(insns, b)
            if kind == BranchKind.CONDITIONAL:
                if warn_only:
                    print("# WARNING: conditional branch at 0x{0:x}: {1:s} -- "
                          "traced path is not guaranteed to represent all inputs"
                          .format(int(frame.pc()), mnemonic), file=sys.stderr)
                else:
                    print("ERROR: conditional branch at 0x{0:x}: {1:s} -- traced "
                          "path is not guaranteed to represent all inputs; pass "
                          "--warn-conditional-branches to continue anyway"
                          .format(int(frame.pc()), mnemonic), file=sys.stderr)
                    sys.exit(1)
            if kind == BranchKind.RETURN:
                print("\t#! <- SP = 0x{0:x}".format(int(frame.read_register("sp"))))
            gdb.execute("stepi", to_string=True)
            debug("After stepi 1")
            print("\t#{:s}".format(mnemonic))
            if kind == BranchKind.CALL:     # calls are handled recursively
                debug("Call")
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
                if ea.get("load") and not ea_only :
                    values = []
                    try :
                        value = gdb.execute("x/{0} 0x{1:x}".format(ea["load"], ea["addr"]), False, True)
                        values.extend(re.findall(r'(0[xX][0-9a-fA-F]+\b)(?!(?:\s+<.*>)?:)', value))
                    except gdb.MemoryError :
                        values.append("'?'")
                    print("\t{0:48s}#! EA = {1:s}; Value = {2}"
                          .format(mnemonic, label(extr.args, ea["addr"]), " ".join(values)))
                else :
                    print("\t{0:48s}#! EA = {1:s}"
                          .format(mnemonic, label(extr.args, ea["addr"])))
            else:
                print("\t{0:s}".format(mnemonic))
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
if "TRACE_OUTFILE" in os.environ:
    sys.stdout = open(os.environ["TRACE_OUTFILE"], "w")

function = os.environ["TRACE_FUNCTION"]
ea_only = "TRACE_EAONLY" in os.environ
warn_only = "TRACE_WARN_BRANCHES" in os.environ

# quirk: even though gdb.Breakpoint is documented to have pending attribute
# it didn't work for me :-(
s = gdb.execute("break *" + function, to_string=True)
if re.search("not defined", s):             # symbol was not found
    print(s.split("\n")[0], file=sys.stderr)
    sys.exit(-1)

# bypass processor capbility detection
gdb.execute("handle SIGILL nostop", to_string=True)

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

gdb.execute("delete breakpoints", to_string=True)
