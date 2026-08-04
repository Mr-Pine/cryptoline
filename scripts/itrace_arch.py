#!/usr/bin/env python3
#
# Architecture-specific instruction classification used by itrace.py,
# factored out into its own module so it can be unit tested without a
# live gdb session (itrace.py's top level always either re-execs into
# gdb or immediately calls gdb.execute(...), so it can't be imported
# directly).

import enum
import re

try:
    import gdb          # real module inside gdb's embedded interpreter
except ImportError:
    gdb = None           # not running under gdb, e.g. under plain unit tests

debug_flag = False

def debug(msg):
    if debug_flag:
        print("DEBUG: {}".format(msg))

bits_to_fmt = {8: 'b', 16: 'h', 32: 'w', 64: 'g'}

def sign_extend(value, bits):
    sign_bit = 1 << bits
    return (value & (sign_bit - 1)) - (value & sign_bit)

def label(args, address):
    min = 4096
    base = None

    for i, (key, value) in enumerate(args.items()):
        offset = address - value
        if offset >= 0 and offset < min:
            min = offset
            base = key
        if offset == 0:
            break

    if base:
        return "L{:s}_0x{:03x}".format(base, min)
    else:   # look above Canonical Frame Address
        offset = args["cfa"] - address
        if offset < 4096:
            return "Lcfa_0x{:03x}".format(offset)

    return "L" + hex(address)

class BranchKind(enum.Enum):
    CALL = 'call'
    RETURN = 'return'
    CONDITIONAL = 'conditional'
    UNCONDITIONAL = 'unconditional'

class Extractor:
    def __init__(self, wordsize):
        self.wordsize = wordsize
        self.mask = (1<<wordsize) - 1
    def printHeader(self, function):
        raise NotImplementedError("Subclasses must override printHeader")
    def isBranch(self, insns, frame):
        # subclass is held responsible for self.branchpattern
        return self.branchpattern.match(insns[0]["asm"])
    def isFunctionCall(self, b):
        raise NotImplementedError("Subclasses must override isFunctionCall")
    def isFunctionReturn(self, b):
        raise NotImplementedError("Subclasses must override isFunctionReturn")
    def isConditionalBranch(self, insns):
        raise NotImplementedError("Subclasses must override isConditionalBranch")
    def getEA(self, insn, frame):
        raise NotImplementedError("Subclasses must override getEA")
    def archUpdate(self, mnemonic, frame):
        pass
    def mnemonic(self, insn):
        return insn["asm"]

    def branch_kind(self, insns, b):
        """Classify a branch instruction already confirmed by isBranch().

        Returns a BranchKind. Calls and returns always take priority over
        the conditional-branch check (e.g. ARM's "bl" starts with "b" but
        must not be treated as a plain conditional/unconditional branch).
        What to actually do about a CONDITIONAL result (error out vs. just
        warn) is a policy decision for the caller, not this classifier.
        """
        if self.isFunctionCall(b):
            return BranchKind.CALL
        if self.isFunctionReturn(b):
            return BranchKind.RETURN
        if self.isConditionalBranch(insns):
            return BranchKind.CONDITIONAL
        return BranchKind.UNCONDITIONAL

class X86_64(Extractor):
    branchpattern = re.compile(r'^(?:repz\s+)?(j\w*|call|ret)q?')
    # e.g. 0x400(%rax,%rbx,8), 0x123(%rdx), etc.
    eapattern = re.compile(r'(-?(?:0x)?[0-9a-f]+)?'         # offset
                           r'\(%([a-z0-9]+)'                # base
                             r'(?:,%([a-z0-9]+),([1248]))?' # index and scale
                           r'\)'
                           r'(?:\s*,\s*%([a-z0-9]+))?')
    args = {}

    def printHeader(self, function):
        frame = gdb.newest_frame()
        print(function + ":")
        for reg in ("rdi", "rsi", "rdx", "rcx", "r8", "r9", "rsp"):
            val = int(frame.read_register(reg)) & 0xffffffffffffffff
            self.args[reg] = val
            print("# %{0:3s} = 0x{1:x}".format(reg, val))
        self.args["cfa"] = self.args["rsp"]
        return

    def isFunctionCall(self, b):
        return b.group(1) == "call"

    def isFunctionReturn(self, b):
        return b.group(1) == "ret"

    def isConditionalBranch(self, insns):
        b = self.branchpattern.match(insns[0]["asm"])
        if not b:
            return False
        mnemonic = b.group(1)
        return mnemonic.startswith("j") and not mnemonic.startswith("jmp")

    def getEA(self, insn, frame):
        mnemonic = insn["asm"]
        if mnemonic.startswith("push") :
            ea = self.eapattern.search("-8(%rsp)")
        elif mnemonic.startswith("pop") :
            ea = self.eapattern.search("(%rsp),%zz")
        else :
            ea = self.eapattern.search(mnemonic)
        if not ea or mnemonic.startswith("lea") :
            return
        addr = 0
        if ea.group(1) : addr = int(ea.group(1), 0)
        if ea.group(2) == "rip" : addr += insn["length"]
        addr += int(frame.read_register(ea.group(2)))
        addr &= 0xffffffffffffffff
        if ea.group(3):
            addr += int(frame.read_register(ea.group(3))) * \
                    int(ea.group(4))
        dst = ea.group(5)
        if dst:
            fmt = "1xg" # default to one 64-bit value
            if dst.startswith("xmm"):
                fmt = "2xg"
            elif dst.startswith("ymm"):
                fmt = "4xg"
            elif dst.startswith("zmm"):
                fmt = "8xg"
            elif mnemonic.startswith("movzb") or mnemonic.startswith("movsb"):
                fmt = "1xb"
            elif dst.startswith("e") or dst.endswith("d"):
                fmt = "1xw"
            return {'addr': addr, 'load': fmt}
        else:
            return {'addr': addr}

class ARM64(Extractor):
    branchpattern = re.compile(r'^(b\.\w+|bl?r?|cbn?z|ret)\b')
    # e.g. [x20,#40], [x20],#8, [x20,x21], [x20, w2, uxtw #3], [x20,x21,lsl#3]
    eapattern = re.compile(r'\[(x[0-9]+|sp)'
                             r'(?:\s*,\s*([xw][0-9]+|#-?(?:0x)?[0-9a-fA-F]+)'
                             r'(?:\s*,\s*(lsl|[su]xtw)(?:\s*#([0-3]))?)?)?'
                           r'\]'
                           r'(?:\s*,\s*#(-?(?:0x)?[0-9a-fA-F]+))?')
    v_to_fmt = {'b': 'b', 'h': 'h', 's': 'w', 'd': 'g'}
    args = {}

    def printHeader(self, function):
        frame = gdb.newest_frame()
        print(function + ":")
        for reg in range(0,8) :
            reg = "x{0}".format(reg)
            val = int(frame.read_register(reg)) & 0xffffffffffffffff
            self.args[reg] = val
            print("# {0} = 0x{1:x}".format(reg, val))
        val = int(frame.read_register("sp")) & 0xffffffffffffffff
        self.args["sp"] = val
        self.args["cfa"] = val
        return

    def isFunctionCall(self, b):
        return b.group(1).startswith("bl")

    def isFunctionReturn(self, b):
        return b.group(1) == "ret"

    def isConditionalBranch(self, insns):
        b = self.branchpattern.match(insns[0]["asm"])
        if not b:
            return False
        mnemonic = b.group(1)
        return mnemonic.startswith("b.") or mnemonic in ("cbz", "cbnz")

    def getEA(self, insn, frame):
        mnemonic = insn["asm"]
        ea = self.eapattern.search(mnemonic)
        if not ea:
            return
        base = ea.group(1)
        offset = ea.group(2)
        adjust = ea.group(3)
        scale = ea.group(4)
        postfix = ea.group(5)
        debug("Effective address: Group 1: %s" % base)
        debug("Effective address: Group 2: %s" % offset)
        base = "%s" % frame.read_register(base)
        debug("Effective address: Base: 0x%x" % int(base,0))
        addr = int(base, 0) & 0xffffffffffffffff
        if offset:
            if offset.startswith("#"):
                offset = int(offset[1:], 0)
            else:
                offset = "%s" % frame.read_register(offset)
                offset = int(offset, 0)
                if adjust == "uxtw":
                    offset &= 0xffffffff
                elif adjust == "sxtw":
                    offset = sign_extend(offset, 31)
                else:
                    offset = sign_extend(offset, 63)
                if scale:
                    offset <<= int(scale)
            debug("Effective address: Offset: 0x%x" % offset)
            addr += offset
        if mnemonic.startswith("ld"):
            fmt = "1xg" # default to one 64-bit value
            if mnemonic.startswith("ldp"):
                fmt = "2xg"
            elif mnemonic.startswith("ldrb") or mnemonic.startswith("ldrsb"):
                fmt = "1xb"
            elif mnemonic.startswith("ldrh") or mnemonic.startswith("ldrsh"):
                fmt = "1xh"
            elif mnemonic.startswith("ldrsw") or re.search(r'w[0-9]+,\s*\[', mnemonic):
                fmt = "1xw"
            else:
                # TODO: multiply by the amount of destination registers?
                v = re.search(r'v[0-9]+\.([1-8]*)([bhsd])', mnemonic)
                if v:
                    fmt = "{}x{}".format(v.group(1) or "1", self.v_to_fmt[v.group(2)])
                # TODO: handle SVE?
            return {'addr': addr, 'load': fmt}
        else:
            return {'addr': addr}

class ARM32(Extractor):
    branchpattern = re.compile(r'^(b(?!f)\w*|cbn?z)\b')
    eapattern = re.compile(r'(?:'
                             r'\[([a-z]+[0-9]*)'
                               r'(?:\s*,\s*([a-z0-9]+|#-?(?:0x)?[0-9a-fA-F]+)|\s*:\d+)?'
                             r'\]'
                           r'|(?:ld|st)m\w*\.?\w*\s+(\w+)!?,)')
    args = {}

    def printHeader(self, function):
        frame = gdb.newest_frame()
        print(function + ":")
        for reg in range(0,4) :
            reg = "r{0}".format(reg)
            val = int(frame.read_register(reg)) & 0xffffffff
            self.args[reg] = val
            print("# {0} = 0x{1:x}".format(reg, val))
        val = int(frame.read_register("sp")) & 0xffffffff
        self.args["sp"] = val
        self.args["cfa"] = val
        return

    def isFunctionCall(self, b):
        return b.group(1).startswith("bl")

    def isFunctionReturn(self, b):
        return b.group(1) == "bx"

    def isConditionalBranch(self, insns):
        b = self.branchpattern.match(insns[0]["asm"])
        if not b:
            return False
        mnemonic = b.group(1)
        if mnemonic.startswith("cb"):
            return True
        if mnemonic.startswith("b") and not mnemonic.startswith("bl") \
                and not mnemonic.startswith("bx"):
            cond = mnemonic[1:]
            return cond not in ("", "al")
        return False

    def getEA(self, insn, frame):
        mnemonic = insn["asm"]
        ea = self.eapattern.search(mnemonic)
        if not ea:
            return
        base = ea.group(1) or ea.group(3)
        offset = ea.group(2)
        debug("Effective address: Group 1: %s" % base)
        debug("Effective address: Group 2: %s" % offset)
        addr = int(frame.read_register(base)) & 0xffffffff
        if base == 'pc':
            isThumb = frame.architecture().name() == 'armv7e-m' or \
                      int(frame.read_register("cpsr")) & 0x20 != 0
            if isThumb:     # is it Thumb?
                addr += 4
            else:
                addr += 8
            addr &= 0xfffffffc
        debug("Effective address: Base: 0x%x" % addr)
        if offset:
            if offset.startswith("#"): offset = offset[1:]
            else: offset = "%s" % frame.read_register(offset)
            debug("Effective address: Offset: 0x%x" % int(offset, 0))
            addr += int(offset, 0)
        if mnemonic.startswith("ld"):
            fmt = "1xw"
            if mnemonic.startswith("ldrb") or mnemonic.startswith("ldrsb"):
                fmt = "1xb"
            elif mnemonic.startswith("ldrh") or mnemonic.startswith("ldrsh"):
                fmt = "1xh"
            # TODO: handle ldmia?
            return {'addr': addr, 'load': fmt}
        elif mnemonic.startswith("vld"):
            if re.search(r'\bq[0-9]+\b', mnemonic):
                return {'addr': addr, 'load': "2xg"}
            else:
                return {'addr': addr, 'load': "1xg"}
        else:
            return {'addr': addr}


class MIPS(Extractor):
    branchpattern = re.compile(r'^(b|j\w*)\s*(.*)')
    # e.g. 20($2)
    eapattern = re.compile(r'(-?(?:0x)?[0-9a-fA-F]+)?\((\w+)\)')
    args = {}

    def printHeader(self, function):
        frame = gdb.newest_frame()
        print(function + ":")
        for reg in range(4,12) :
            reg = "r{0}".format(reg)
            val = int(frame.read_register(reg)) & self.mask
            self.args[reg] = val
            print("# {0} = 0x{1:x}".format(reg, val))
        val = int(frame.read_register("sp")) & self.mask
        self.args["sp"] = val
        self.args["cfa"] = val
        return

    def isBranch(self, insns, frame):
        b = self.branchpattern.match(insns[0]["asm"])
        if b:
            # trace instruction in delay slot, as gdb fails to do so
            mnemonic = insns[1]["asm"]
            ea = self.getEA(insns[1], frame)
            if ea:
                print("\t{0:48s}#! EA = {1:s}".format(mnemonic, label(self.args, ea["addr"])))
            else:
                print("\t{0:s}".format(mnemonic))
        return b

    def isFunctionCall(self, b):
        # MIPS calls are "jal"/"jalr"; branchpattern's "b" alternative only
        # ever matches the bare literal "b" (never "bl"-anything), so a
        # "bl" check here (copy-pasted from the ARM extractor) never fires.
        return b.group(1).startswith("jal")

    def isFunctionReturn(self, b):
        # gdb disassembles the return-address register as "$ra", not "ra".
        return b.group(1) == "jr" and b.group(2).lstrip("$") == "ra"

    def isConditionalBranch(self, insns):
        # branchpattern's "b|j\w*" alternation collapses any condition
        # suffix (e.g. "beq") into group 2, so classify from the bare
        # mnemonic token instead.
        mnemonic = insns[0]["asm"].split()[0]
        if not mnemonic.startswith("b"):
            return False
        return mnemonic not in ("b", "bal")

    def getEA(self, insn, frame):
        mnemonic = insn["asm"]
        ea = self.eapattern.search(mnemonic)
        if not ea:
            return
        base = ea.group(2)
        offset = ea.group(1)
        debug("Effective address: Group 1: %s" % base)
        debug("Effective address: Group 2: %s" % offset)
        addr = int(frame.read_register(base)) & self.mask
        debug("Effective address: Base: 0x%x" % addr)
        if offset:
            debug("Effective address: Offset: 0x%x" % int(offset, 0))
            addr += int(offset, 0)
        if mnemonic.startswith("l") :
            fmt = "1x{}".format(bits_to_fmt[self.wordsize])
            return {'addr': addr, 'load': fmt}
        else :
            return {'addr': addr}

class RISCV(Extractor):
    branchpattern = re.compile(r'^(b|j\w*|ret)\s*(.*)')
    # e.g. 20($2)
    eapattern = re.compile(r'(-?(?:0x)?[0-9a-fA-F]+)?\((\w+)\)')
    args = {}

    def printHeader(self, function):
        frame = gdb.newest_frame()
        print(function + ":")
        for reg in range(10,18) :
            reg = "x{0}".format(reg)
            val = int(frame.read_register(reg)) & self.mask
            self.args[reg] = val
            print("# {0} = 0x{1:x}".format(reg, val))
        val = int(frame.read_register("sp")) & self.mask
        self.args["sp"] = val
        self.args["cfa"] = val
        return

    def isFunctionCall(self, b):
        return b.group(1).startswith("jal")

    def isFunctionReturn(self, b):
        return b.group(1) == "ret"

    def isConditionalBranch(self, insns):
        # RISC-V has no unconditional mnemonic starting with "b" --
        # unconditional control transfer is always j/jal/jalr/ret -- so
        # any bare "b*" token is one of beq/bne/blt/bge/bltu/bgeu (or
        # their zero-compare pseudo-ops).
        mnemonic = insns[0]["asm"].split()[0]
        return mnemonic.startswith("b")

    def getEA(self, insn, frame):
        mnemonic = insn["asm"]
        ea = self.eapattern.search(mnemonic)
        if not ea:
            return
        base = ea.group(2)
        offset = ea.group(1)
        debug("Effective address: Group 1: %s" % base)
        debug("Effective address: Group 2: %s" % offset)
        addr = int(frame.read_register(base)) & self.mask
        debug("Effective address: Base: 0x%x" % addr)
        if offset:
            debug("Effective address: Offset: 0x%x" % int(offset, 0))
            addr += int(offset, 0)
        if mnemonic.startswith("l"):
            fmt = "1x{}".format(bits_to_fmt[self.wordsize])
            if mnemonic.starswith("lb"):
                fmt = "1xb"
            elif mnemonic.starswith("lh"):
                fmt = "1xh"
            elif mnemonic.starswith("lw"):
                fmt = "1xw"
            return {'addr': addr, 'load': fmt}
        elif mnemonic.startswith("vl"):
            # TODO: multiply by the amount of destination registers for vlseg?
            return {'addr': addr, 'load': "{}x{}".format(self.vlen, bits_to_fmt[self.vsew])}
        else:
            return {'addr': addr}

    vsew = -1
    vlen = 0
    vlmul = 0
    vsetpattern = re.compile(r'^vseti*vli*\s+([a-z0-9]+),\s*([a-z0-9]+),\s*(.*)')

    def archUpdate(self, mnemonic, frame):
        vset = self.vsetpattern.search(mnemonic)
        if not vset:
            return

        # handle vlen
        if vset.group(1) != "zero":
            self.vlen = frame.read_register(vset.group(1))
        else:
            if vset.group(2).isnumeric():
                self.vlen = vset.group(2)
            else:
                self.vlen = frame.read_register(vset.group(2))

        # handle vsew and vlmul
        if vset.group(3).startswith("e"):
            vtype = re.match(r'e([1-8]+),\s*(mf*)([1248]),.*', vset.group(3))
            self.vsew = int(vtype.group(1))
            if vtype.group(2) == "mf": # fraction, round up to 1
                self.vlmul = 1
            else:
                self.vlmul = int(vtype.group(3))
        else:
            vtype = frame.read_register(vset.group(3))
            self.vsew = 8 << ((vtype >> 3) & 0b111)
            if vtype & 0b100:          # fraction, round up to 1
                self.vlmul = 1
            else:
                self.vlmul = 1 << (vtype & 0b11)

    vecpattern = re.compile(r'^(v[a-z][a-z0-9]+\.v[a-z]*)(\s+v([0-9]+))(,.*)')
    segpattern = re.compile(r'^v[ls]seg([2-8])e[0-9]+\.v')

    def mnemonic(self, insn):
        mnemonic = insn["asm"]
        vec = self.vecpattern.search(mnemonic)
        if not vec:
            return mnemonic
        # extend vector instructions with vsew and vlen
        mnemonic = "{0:s}({1}x{2}/{3})".format(vec.group(1), self.vlen, self.vsew, self.vlmul)
        mnemonic += vec.group(2)
        # extend vector register for segmented load/stores
        seg = self.segpattern.search(vec.group(1))
        if seg:
            mnemonic += "..{}".format(int(vec.group(3)) + int(seg.group(1)) - 1)
        return "{0:s}{1:s}".format(mnemonic, vec.group(4))
