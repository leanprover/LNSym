/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Shilpi Goel
-/
import Arm.BitVec

namespace aes_helpers

open Std.BitVec

def aes_shift_rows (op : BitVec 128) : BitVec 128 :=
  let op_7_0     := BitVec.extract op 7 0
  let op_47_40   := BitVec.extract op 47 40
  let op_87_80   := BitVec.extract op 87 80
  let op_127_120 := BitVec.extract op 127 120
  let op_39_32   := BitVec.extract op 39 32
  let op_79_72   := BitVec.extract op 79 72
  let op_119_112 := BitVec.extract op 119 112
  let op_31_24   := BitVec.extract op 31 24
  let op_71_64   := BitVec.extract op 71 64
  let op_111_104 := BitVec.extract op 111 104
  let op_23_16   := BitVec.extract op 23 16
  let op_63_56   := BitVec.extract op 63 56
  let op_103_96  := BitVec.extract op 103 96
  let op_15_8    := BitVec.extract op 15 8
  let op_55_48   := BitVec.extract op 55 48
  let op_95_88   := BitVec.extract op 95 88
  (op_95_88 ++ op_55_48 ++ op_15_8 ++ op_103_96 ++ op_63_56 ++
  op_23_16 ++ op_111_104 ++ op_71_64 ++ op_31_24 ++ op_119_112 ++
  op_79_72 ++ op_39_32 ++ op_127_120 ++ op_87_80 ++ op_47_40 ++
  op_7_0)

-- S-box values
def gf2_list : List (BitVec 128) :=
        [
        0x16bb54b00f2d99416842e6bf0d89a18c#128, -- <127:0>
        0xdf2855cee9871e9b948ed9691198f8e1#128, -- <127:0>
        0x9e1dc186b95735610ef6034866b53e70#128, -- <127:0>
        0x8a8bbd4b1f74dde8c6b4a61c2e2578ba#128, -- <127:0>
        0x08ae7a65eaf4566ca94ed58d6d37c8e7#128, -- <127:0>
        0x79e4959162acd3c25c2406490a3a32e0#128, -- <127:0>
        0xdb0b5ede14b8ee4688902a22dc4f8160#128, -- <127:0>
        0x73195d643d7ea7c41744975fec130ccd#128, -- <127:0>
        0xd2f3ff1021dab6bcf5389d928f40a351#128, -- <127:0>
        0xa89f3c507f02f94585334d43fbaaefd0#128, -- <127:0>
        0xcf584c4a39becb6a5bb1fc20ed00d153#128, -- <127:0>
        0x842fe329b3d63b52a05a6e1b1a2c8309#128, -- <127:0>
        0x75b227ebe28012079a059618c323c704#128, -- <127:0>
        0x1531d871f1e5a534ccf73f362693fdb7#128, -- <127:0>
        0xc072a49cafa2d4adf04759fa7dc982ca#128, -- <127:0>
        0x76abd7fe2b670130c56f6bf27b777c63#128  -- <127:0>
        ]

def bitvec_list_concat (xs : List (BitVec n)) : BitVec (n * List.length xs) :=
    match xs with
    | [] => 0#0
    | x :: rest =>
      have h1: (n + n * List.length rest) = (n * List.length (x :: rest)) := by sorry
      h1 ▸ (x ++ (bitvec_list_concat rest))

def gf2 : BitVec (128 * 16) := bitvec_list_concat gf2_list

end aes_helpers
