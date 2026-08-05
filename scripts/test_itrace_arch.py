#!/usr/bin/env python3
#
# Unit tests for the branch classification logic in itrace_arch.py.
# Plain unittest (no pytest dependency) so this runs anywhere with
# python3 and does not require gdb: itrace_arch.py has no top-level
# gdb calls, only method bodies that touch `gdb`/a live frame, which
# none of the methods under test here do.
#
# Run with: python3 -m unittest scripts/test_itrace_arch.py -v

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import itrace_arch
from itrace_arch import X86_64, ARM64, ARM32, MIPS, RISCV, BranchKind, \
                        MemoryMap, ea_annotation, segment


def insns(asm):
    return [{"asm": asm}]


class X86_64BranchTest(unittest.TestCase):
    def setUp(self):
        self.extr = X86_64(64)

    def test_conditional_jumps_are_conditional(self):
        for asm in ("jne    0x401030", "je     0x401030", "jg     0x401030"):
            with self.subTest(asm=asm):
                self.assertTrue(self.extr.isConditionalBranch(insns(asm)))

    def test_unconditional_jump_is_not_conditional(self):
        self.assertFalse(self.extr.isConditionalBranch(insns("jmp    0x401030")))
        self.assertFalse(self.extr.isConditionalBranch(insns("jmpq   0x401030")))

    def test_call_and_ret_are_not_conditional(self):
        self.assertFalse(self.extr.isConditionalBranch(insns("call   0x401000 <bar>")))
        self.assertFalse(self.extr.isConditionalBranch(insns("retq")))

    def test_non_branch_is_not_conditional(self):
        self.assertFalse(self.extr.isConditionalBranch(insns("mov    %rax,%rbx")))

    def test_branch_kind(self):
        cases = {
            "jne    0x401030": BranchKind.CONDITIONAL,
            "jmp    0x401030": BranchKind.UNCONDITIONAL,
            "call   0x401000 <bar>": BranchKind.CALL,
            "retq": BranchKind.RETURN,
        }
        for asm, expected in cases.items():
            with self.subTest(asm=asm):
                b = self.extr.isBranch(insns(asm), None)
                self.assertEqual(self.extr.branch_kind(insns(asm), b), expected)


class ARM64BranchTest(unittest.TestCase):
    def setUp(self):
        self.extr = ARM64(64)

    def test_conditional(self):
        for asm in ("b.eq   0x400abc", "b.ne   0x400abc",
                    "cbz    x0, 0x400abc", "cbnz   x0, 0x400abc"):
            with self.subTest(asm=asm):
                self.assertTrue(self.extr.isConditionalBranch(insns(asm)))

    def test_not_conditional(self):
        for asm in ("b      0x400abc", "bl     0x400000 <foo>",
                    "blr    x1", "br     x2", "ret"):
            with self.subTest(asm=asm):
                self.assertFalse(self.extr.isConditionalBranch(insns(asm)))

    def test_branch_kind_call_wins_over_conditional_lookalike(self):
        # "bl" starts with "b" but must classify as a call, not conditional
        asm = "bl     0x400000 <foo>"
        b = self.extr.isBranch(insns(asm), None)
        self.assertEqual(self.extr.branch_kind(insns(asm), b), BranchKind.CALL)


class ARM32BranchTest(unittest.TestCase):
    def setUp(self):
        self.extr = ARM32(32)

    def test_conditional(self):
        for asm in ("beq    0x1030", "bne.n  0x1030", "bne.w  0x1030",
                    "cbz    r0, 0x1030", "cbnz   r1, 0x1030"):
            with self.subTest(asm=asm):
                self.assertTrue(self.extr.isConditionalBranch(insns(asm)))

    def test_not_conditional(self):
        for asm in ("b      0x1030", "bal    0x1030",
                    "bl     0x1000 <foo>", "bx     lr"):
            with self.subTest(asm=asm):
                self.assertFalse(self.extr.isConditionalBranch(insns(asm)))

    def test_branch_kind_return(self):
        asm = "bx     lr"
        b = self.extr.isBranch(insns(asm), None)
        self.assertEqual(self.extr.branch_kind(insns(asm), b), BranchKind.RETURN)


class MIPSBranchTest(unittest.TestCase):
    def setUp(self):
        self.extr = MIPS(32)

    def test_conditional(self):
        for asm in ("beq    $2,$3,0x1030", "bne    $2,$3,0x1030",
                    "bgtz   $2,0x1030"):
            with self.subTest(asm=asm):
                self.assertTrue(self.extr.isConditionalBranch(insns(asm)))

    def test_not_conditional(self):
        for asm in ("b      0x1030", "bal    0x1030",
                    "j      0x1030", "jal    0x1030", "jr     $ra"):
            with self.subTest(asm=asm):
                self.assertFalse(self.extr.isConditionalBranch(insns(asm)))

    def test_branch_kind_conditional(self):
        # Built directly via branchpattern rather than isBranch(): MIPS's
        # isBranch also prints the delay-slot instruction, which needs a
        # 2-instruction window and (for loads/stores) a live frame -- both
        # irrelevant to branch_kind's classification, which is all this
        # test cares about.
        asm = "beq    $2,$3,0x1030"
        b = self.extr.branchpattern.match(asm)
        self.assertEqual(self.extr.branch_kind(insns(asm), b), BranchKind.CONDITIONAL)

    def test_is_function_call(self):
        for asm in ("jal    0x400000 <foo>", "jalr   $25"):
            with self.subTest(asm=asm):
                b = self.extr.branchpattern.match(asm)
                self.assertTrue(self.extr.isFunctionCall(b))

    def test_is_function_return(self):
        b = self.extr.branchpattern.match("jr     $ra")
        self.assertTrue(self.extr.isFunctionReturn(b))


class RISCVBranchTest(unittest.TestCase):
    def setUp(self):
        self.extr = RISCV(64)

    def test_conditional(self):
        for asm in ("beq    a0,a1,0x1030", "bne    a0,a1,0x1030",
                    "bltu   a0,a1,0x1030"):
            with self.subTest(asm=asm):
                self.assertTrue(self.extr.isConditionalBranch(insns(asm)))

    def test_not_conditional(self):
        for asm in ("j      0x1030", "jal    ra,0x1030",
                    "jalr   ra,a0,0", "ret"):
            with self.subTest(asm=asm):
                self.assertFalse(self.extr.isConditionalBranch(insns(asm)))

    def test_branch_kind_conditional(self):
        asm = "beq    a0,a1,0x1030"
        b = self.extr.isBranch(insns(asm), None)
        self.assertEqual(self.extr.branch_kind(insns(asm), b), BranchKind.CONDITIONAL)


class MemoryMapTest(unittest.TestCase):
    SECTIONS = """\
Exec file: `/tmp/seg', file type elf64-x86-64.
 [11]     0x555555555000->0x55555555501b at 0x00001000: .init ALLOC LOAD READONLY CODE HAS_CONTENTS
 [15]     0x555555555080->0x55555555522a at 0x00001080: .text ALLOC LOAD READONLY CODE HAS_CONTENTS
 [17]     0x555555556000->0x555555556004 at 0x00002000: .rodata ALLOC LOAD READONLY DATA HAS_CONTENTS
 [24]     0x555555558000->0x555555558018 at 0x00003000: .data ALLOC LOAD DATA HAS_CONTENTS
 [25]     0x555555558018->0x555555558028 at 0x00003018: .bss ALLOC
 [26]     0x0000000000->0x000000002b at 0x00003018: .comment READONLY HAS_CONTENTS
Object file: /usr/lib/x86_64-linux-gnu/libc.so.6
 [17]     0x00007ffff7c28000->0x00007ffff7db0000 at 0x00028000: .text ALLOC LOAD READONLY CODE HAS_CONTENTS
"""
    MAPPINGS = """\
process 433194
Mapped address spaces:

Start Addr         End Addr           Size               Offset             Perms File\x20
0x0000555555554000 0x0000555555555000 0x1000             0x0                r--p  /tmp/seg\x20
0x0000555555559000 0x000055555557a000 0x21000            0x0                rw-p  [heap]\x20
0x00007ffff7c28000 0x00007ffff7db0000 0x188000           0x28000            r-xp  /usr/lib/x86_64-linux-gnu/libc.so.6\x20
0x00007ffff7e05000 0x00007ffff7e12000 0xd000             0x0                rw-p  \x20
0x00007ffffffde000 0x00007ffffffff000 0x21000            0x0                rw-p  [stack]\x20
"""

    def setUp(self):
        self.map = MemoryMap()
        self.map.sections = MemoryMap.parse_sections(self.SECTIONS)
        self.map.mappings = MemoryMap.parse_mappings(self.MAPPINGS)
        self.map.loaded = True

    def test_sections_win_over_mappings(self):
        # both sources cover this address, the section is the finer answer
        self.assertEqual(self.map.lookup(0x555555554000 + 0x1100), ".text")

    def test_section_boundaries(self):
        self.assertEqual(self.map.lookup(0x555555558018), ".bss")
        self.assertEqual(self.map.lookup(0x555555558027), ".bss")
        self.assertEqual(self.map.lookup(0x555555558017), ".data")

    def test_non_alloc_sections_are_ignored(self):
        self.assertIsNone(self.map.find(self.map.sections, 0x10))

    def test_mappings(self):
        self.assertEqual(self.map.lookup(0x7ffffffde000), "[stack]")
        self.assertEqual(self.map.lookup(0x555555560000), "[heap]")
        # a bare ".text" is always the executable's own
        self.assertEqual(self.map.lookup(0x7ffff7c28100), "libc.so.6:.text")
        self.assertEqual(self.map.lookup(0x7ffff7e05000), "anon")
        self.assertEqual(self.map.lookup(0x555555554100), "seg")

    def test_unknown_address(self):
        # without gdb the re-read of the map yields nothing
        self.assertIsNone(self.map.lookup(0x1234))
        self.assertIn(0x1234 >> 12, self.map.unmapped)
        self.assertEqual(segment(0x1234), "?")

    def test_annotation(self):
        args = {"rsp": 0x7fffffffe000, "cfa": 0x7fffffffe000}
        itrace_arch.memory_map = self.map
        try:
            self.assertEqual(ea_annotation(args, 0x7fffffffe008),
                             "EA = Lrsp_0x008; Segment = [stack]")
        finally:
            itrace_arch.memory_map = MemoryMap()


if __name__ == "__main__":
    unittest.main()
