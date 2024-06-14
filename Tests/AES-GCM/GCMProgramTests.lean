/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.BitVec
import Arm.Exec
import Arm.Cfg.Cfg
import Tests.Common
import Tests.«AES-GCM».GCMGhashV8Program
import Tests.«AES-GCM».GCMGmultV8Program
import Tests.«AES-GCM».GCMInitV8Program

open BitVec

-- Tests are taken from AWS-LC's ABI tests for these assembly routines

-- Test generation:
--   Compile AWS-LC:
--     0. export CC=clang; export CXX=clang++ (make sure clang version is 10+)
--     1. mkdir aws-lc-build; cd aws-lc-build
--     2. cmake3 -GNinja \
--           -DKEEP_ASM_LOCAL_SYMBOLS=1 \
--           -DCMAKE_BUILD_TYPE=Release\
--           -DCMAKE_INSTALL_PREFIX=../aws-lc-install \
--           ../../aws-lc
--     3. ninja-build
--   Run test:
--     1. aws-lc-build/crypto/crypto_test --gtest_filter="GCMTest.ABI"

/-
  How to get the number of steps to run for a program?

  When a program finishes, ArmState.pc would be set to 0x0#64 and ArmState.error
  will be `StateError.None`. If a program hasn't reached the last instruction,
  its ArmState.pc will be some number other than 0x0#64. This is based on an
  assumption that programs don't typically start at pc 0x0#64.
  If a program runs past the last instruction, its ArmState.error will be:

    StateError.NotFound "No instruction found at PC 0x0000000000000000#64!"

  Based on above information, we could do a binary search for the number of steps
  to run a program and the stopping criterion is that ArmState.pc = 0x0#64 and
  ArmState.error = StateError.None. This sounds awfully programmable, but for
  now we reply on this comment.

-/

namespace GCMProgramTestParams

def H_address := 0#64
def x_address := 0x10#64
def Htable_address := 0x20#64
def In_address := 0x120#64

def H : List (BitVec 64) :=
  [ 0x66e94bd4ef8a2c3b#64, 0x884cfa59ca342b2e#64 ]

def Htable_before_init : List (BitVec 64) := List.replicate 32 0x0#64

def Htable : List (BitVec 64) :=
  [ 0x1099f4b39468565c#64, 0xcdd297a9df145877#64,
    0xdd4b631a4b7c0e2b#64, 0x62d81a7fe5da3296#64,
    0xea0b3a488cb9209b#64, 0x88d320376963120d#64,
    0x35c1a04f8bfb2395#64, 0x8695e702c322faf9#64,
    0xb354474d48d9d96c#64, 0xb2261b4d0cb1e020#64,
    0xe4adc23e440c7165#64, 0x568bd97348bd9145#64,
    0x7d845b630bb0a55d#64, 0xf9151b1f632d10b4#64,
    0x8491407c689db5e9#64, 0xa674eba8f9d7f250#64,
    0x4af32418184aee1e#64, 0xec87cfb0e19d1c4e#64,
    0xf109e6e0b31d1eee#64, 0x7d1998bcfc545474#64,
    0x8c107e5c4f494a9a#64, 0x7498729da40cd280#64,
    0xa47c653dfbeac924#64, 0xd0e417a05fe61ba4#64,
    0x0#64, 0x0#64,
    0x0#64, 0x0#64,
    0x0#64, 0x0#64,
    0x0#64, 0x0#64 ]

def buf : List (BitVec 64) :=
  List.replicate 14 0x2a2a2a2a2a2a2a2a#64

def X : List (List (BitVec 8)) :=
  [ [ 0x10#8, 0x54#8, 0x43#8, 0xb0#8, 0x2c#8, 0x4b#8, 0x1f#8, 0x24#8,
      0x3b#8, 0xcd#8, 0xd4#8, 0x87#8, 0x16#8, 0x65#8, 0xb3#8, 0x2b#8 ], -- initial X
    [ 0xa2#8, 0xc9#8, 0x9c#8, 0x56#8, 0xeb#8, 0xa7#8, 0x91#8, 0xf6#8,
      0x9e#8, 0x15#8, 0xa6#8, 0x00#8, 0x67#8, 0x29#8, 0x7e#8, 0x0f#8 ], -- X after gcm_gmult_v8
    [ 0x20#8, 0x60#8, 0x2e#8, 0x75#8, 0x7a#8, 0x4e#8, 0xec#8, 0x90#8,
      0xc0#8, 0x9d#8, 0x49#8, 0xfd#8, 0xdc#8, 0xf2#8, 0xc9#8, 0x35#8 ], -- X after gcm_ghash_v8 with 1block
    [ 0x0d#8, 0x7e#8, 0xc1#8, 0x6a#8, 0x81#8, 0x31#8, 0x18#8, 0xa0#8,
      0xcb#8, 0x8b#8, 0x58#8, 0x01#8, 0xb6#8, 0x65#8, 0xd1#8, 0x61#8 ], -- X after gcm_ghash_v8 with 2blocks
    [ 0xc6#8, 0x82#8, 0xf8#8, 0xb2#8, 0x88#8, 0x36#8, 0xe6#8, 0x66#8,
      0x19#8, 0xdb#8, 0x10#8, 0xbf#8, 0xdb#8, 0xca#8, 0x73#8, 0x37#8 ], -- X after gcm_ghash_v8 with 3blocks
    [ 0xc7#8, 0xb3#8, 0x21#8, 0xfc#8, 0x7c#8, 0x11#8, 0xf1#8, 0x79#8,
      0x38#8, 0x0a#8, 0xe9#8, 0x4e#8, 0x74#8, 0xbe#8, 0x18#8, 0xde#8 ], -- X after gcm_ghash_v8 with 4blocks
    [ 0xdd#8, 0x22#8, 0x38#8, 0x13#8, 0x5a#8, 0x16#8, 0xf4#8, 0x96#8,
      0xf9#8, 0xf5#8, 0x61#8, 0x02#8, 0x76#8, 0xad#8, 0xdc#8, 0x16#8 ], -- X after gcm_ghash_v8 with 5blocks
    [ 0xd4#8, 0xea#8, 0x47#8, 0x79#8, 0x16#8, 0xdf#8, 0x38#8, 0x56#8,
      0x6d#8, 0x7d#8, 0x8a#8, 0x0d#8, 0x3f#8, 0x30#8, 0xcf#8, 0x0d#8 ], -- X after gcm_ghash_v8 with 6blocks
    [ 0x7d#8, 0x4f#8, 0x74#8, 0xca#8, 0x86#8, 0x1c#8, 0xbb#8, 0xaa#8,
      0x96#8, 0x10#8, 0x2b#8, 0x95#8, 0x7a#8, 0xc0#8, 0xce#8, 0x7b#8 ] -- X after gcm_ghash_v8 with 7blocks
  ]

end GCMProgramTestParams



-- Test gcm_init_v8
namespace GCMInitV8ProgramTest

open GCMProgramTestParams

def init_gpr : Store (BitVec 5) (BitVec 64) :=
  fun i =>
    match i with
      | 0 => Htable_address
      | 1 => H_address
      | _ => 0#64

def init_gcm_init_test : ArmState :=
  let s := { gpr := init_gpr,
             sfp := (fun (_ : BitVec 5) => 0#128),
             pc := 0x7aa1c0#64,
             pstate := zero_pstate,
             mem := (fun (_ :BitVec 64) => 0#8),
             program := GCMInitV8Program.gcm_init_v8_program,
             error := StateError.None
           }
  let s := write_mem_bytes 16 H_address (revflat H) s
  let s := write_mem_bytes 256 Htable_address (revflat Htable_before_init) s
  s

def final_state : ArmState := run GCMInitV8Program.gcm_init_v8_program.length init_gcm_init_test
def final_pc : BitVec 64 := final_state.pc
def final_table : BitVec 2048 := read_mem_bytes 256 Htable_address final_state
example : final_table = revflat Htable := by native_decide
example : final_state.error = StateError.None := by native_decide

end GCMInitV8ProgramTest


-- Test gcm_gmult_v8
namespace GCMGmultV8ProgramTest

open GCMProgramTestParams

def X_before : List (BitVec 8) := List.get! X 0
def flat_X_before := revflat X_before
def X_after : List (BitVec 8) := List.get! X 1

def gcm_gmult_final_state : ArmState :=
  let init_gpr :=
    fun i =>
      match i with
        | 0 => x_address
        | 1 => Htable_address
        | _ => 0#64
  let s := { gpr := init_gpr,
             sfp := (fun (_ : BitVec 5) => 0#128),
             pc  := 0x7aa420#64,
             pstate := zero_pstate,
             mem := (fun (_ : BitVec 64) => 0#8),
             program := GCMGmultV8Program.gcm_gmult_v8_program,
             error := StateError.None
            }
  let s := write_mem_bytes 16 x_address flat_X_before s
  have h : 2048 = (128 * 16 / 8) * 8 := by decide
  let s := write_mem_bytes (128 * 16 / 8) Htable_address (h ▸ (revflat Htable)) s
  let final_state := run GCMGmultV8Program.gcm_gmult_v8_program.length s
  final_state

def final_hash : BitVec 128 := read_mem_bytes 16 x_address gcm_gmult_final_state

example : final_hash = revflat X_after := by native_decide
example : gcm_gmult_final_state.error = StateError.None := by native_decide

end GCMGmultV8ProgramTest



namespace GCMGhashV8ProgramTest

open GCMProgramTestParams

def gcm_ghash_test (n : Nat) (len : BitVec 64) (buf : BitVec 896)
  (X_before : BitVec 128) : ArmState :=
  let init_gpr : Store (BitVec 5) (BitVec 64) :=
    fun i =>
      match i with
        | 0 => x_address
        | 1 => Htable_address
        | 2 => In_address
        | 3 => len
        | _ => 0#64
  let s := { gpr := init_gpr,
             sfp := (fun (_ : BitVec 5) => 0#128),
             pc := 0x7aa490#64,
             pstate := zero_pstate,
             mem := (fun (_ :BitVec 64) => 0#8),
             program := GCMGhashV8Program.gcm_ghash_v8_program,
             error := StateError.None
           }
  let s := write_mem_bytes 16 x_address X_before s
  have h : 2048 = (128 * 16 / 8) * 8 := by decide
  let s := write_mem_bytes (128 * 16 / 8) Htable_address (h ▸ (revflat Htable)) s
  let s := write_mem_bytes 112 In_address buf s
  let final_state := run n s
  final_state

-- Test gcm_ghash_v8 for 2 blocks of input
namespace block2
def len := 0x20#64

def X_before : List (BitVec 8) := List.get! X 2
def X_after : List (BitVec 8) := List.get! X 3

def final_state : ArmState :=
  gcm_ghash_test 68 len (revflat buf) (revflat X_before)
def final_hash : BitVec 128 := read_mem_bytes 16 x_address final_state

example : final_hash = revflat X_after := by native_decide
example : final_state.error = StateError.None := by native_decide

end block2

-- Test gcm_ghash_v8 for 4 blocks of input
namespace block4
def len := 0x40#64

def X_before : List (BitVec 8) := List.get! X 4
def X_after : List (BitVec 8) := List.get! X 5

def final_state : ArmState :=
  gcm_ghash_test 63 len (revflat buf) (revflat X_before)
def final_hash : BitVec 128 := read_mem_bytes 16 x_address final_state

example : final_hash = revflat X_after := by native_decide
example : final_state.error = StateError.None := by native_decide

end block4

-- Test gcm_ghash_v8 for 5 blocks of input
namespace block5
def len := 0x50#64

def X_before : List (BitVec 8) := List.get! X 5
def X_after : List (BitVec 8) := List.get! X 6

def final_state : ArmState :=
  gcm_ghash_test 86 len (revflat buf) (revflat X_before)
def final_hash : BitVec 128 := read_mem_bytes 16 x_address final_state

example : final_hash = revflat X_after := by native_decide
example : final_state.error = StateError.None := by native_decide

end block5

-- Test gcm_ghash_v8 for 6 blocks of input
namespace block6
def len := 0x60#64

def X_before : List (BitVec 8) := List.get! X 6
def X_after : List (BitVec 8) := List.get! X 7

def final_state : ArmState :=
  gcm_ghash_test 97 len (revflat buf) (revflat X_before)
def final_hash : BitVec 128 := read_mem_bytes 16 x_address final_state

example : final_hash = revflat X_after := by native_decide
example : final_state.error = StateError.None := by native_decide

end block6

-- Test gcm_ghash_v8 for 7 blocks of input
namespace block7
def len := 0x70#64

def X_before : List (BitVec 8) := List.get! X 7
def X_after : List (BitVec 8) := List.get! X 8

def final_state : ArmState :=
  gcm_ghash_test 106 len (revflat buf) (revflat X_before)
def final_hash : BitVec 128 := read_mem_bytes 16 x_address final_state

example : final_hash = revflat X_after := by native_decide
example : final_state.error = StateError.None := by native_decide

end block7

end GCMGhashV8ProgramTest
