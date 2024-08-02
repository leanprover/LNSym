/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.BitVec
import Arm.Exec
import Arm.Cfg.Cfg
import Tests.Common
import Tests.«AES-GCM».AESHWSetEncryptKeyProgram
import Tests.«AES-GCM».AESHWEncryptProgram
import Tests.«AES-GCM».AESHWCtr32EncryptBlocksProgram

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
--     1. aws-lc-build/crypto/crypto_test --gtest_filter="AESTest.ABI"

/-
  How to get the number of steps to run for a program?

  When a program finishes, ArmState.pc would be set to 0x0#64 and `read_err ArmState`
  will be `StateError.None`. If a program hasn't reached the last instruction,
  its ArmState.pc will be some number other than 0x0#64. This is based on an
  assumption that programs don't typically start at pc 0x0#64.
  If a program runs past the last instruction, `(read_err ArmState)` will be:

    StateError.NotFound "No instruction found at PC 0x0000000000000000#64!"

  Based on above information, we could do a binary search for the number of steps
  to run a program and the stopping criterion is that ArmState.pc = 0x0#64 and
  `read_err ArmState = StateError.None`. This sounds awfully programmable, but for
  now we reply on this comment.

-/


namespace AESHWSetEncryptKeyProgramTest

-- The assembly checks that kKey address cannot be 0, so we add 8 to the address
def kKey_address : BitVec 64 := 0#64 + 8#64

def kKey : List (BitVec 8) := List.replicate 32 0x00#8

-- Start address for the AES_KEY struct
def key_address : BitVec 64 := 128#64 + 8#64

-- The .Lrcon constant defined in aesv8-armx.S
def rcon : List (BitVec 32) :=
[ 0x01#32, 0x01#32, 0x01#32, 0x01#32,
  0x0c0f0e0d#32, 0x0c0f0e0d#32, 0x0c0f0e0d#32, 0x0c0f0e0d#32,
  0x1b#32, 0x1b#32, 0x1b#32, 0x1b#32
]

def rcon_address : BitVec 64 := 0x4002ca0#64


def aes_hw_set_encrypt_key_test (n : Nat) (key_bits : BitVec 64) : ArmState :=
  let init_gpr : Store (BitVec 5) (BitVec 64) :=
    fun i =>
      match i with
        | 0 => kKey_address
        | 1 => key_bits
        | 2 => key_address
        | _ => 0#64
  let s := { gpr := init_gpr,
             sfp := (fun (_ : BitVec 5) => 0#128),
             pc := 0x79f380#64,
             pstate := PState.zero,
             mem := (fun (_ :BitVec 64) => 0#8),
             program := AESHWSetEncryptKeyProgram.aes_hw_set_encrypt_key_program,
             error := StateError.None
          }
  -- write kKey
  let s := write_mem_bytes 32 kKey_address (revflat kKey) s
  -- write rcon
  let s := write_mem_bytes 48 rcon_address (revflat rcon) s
  let final_state := run n s
  final_state


namespace AES128

def key_bits : BitVec 64 := 128#64
def rounds : BitVec 64 := 10#64
def rd_key : List (BitVec 32) :=
  [ 0x00#32, 0x00#32, 0x00#32, 0x00#32,
    0x63636362#32, 0x63636362#32, 0x63636362#32, 0x63636362#32,
    0xc998989b#32, 0xaafbfbf9#32, 0xc998989b#32, 0xaafbfbf9#32,
    0x50349790#32, 0xfacf6c69#32, 0x3357f4f2#32, 0x99ac0f0b#32,
    0x7bda06ee#32, 0x81156a87#32, 0xb2429e75#32, 0x2bee917e#32,
    0x882b2e7f#32, 0x93e44f8#32, 0xbb7cda8d#32, 0x90924bf3#32,
    0x854b61ec#32, 0x8c752514#32, 0x3709ff99#32, 0xa79bb46a#32,
    0x87177521#32, 0xb625035#32, 0x3c6bafac#32, 0x9bf01bc6#32,
    0x3303f90e#32, 0x3861a93b#32, 0x40a0697#32, 0x9ffa1d51#32,
    0xe2d8d4b1#32, 0xdab97d8a#32, 0xdeb37b1d#32, 0x4149664c#32,
    0xcb5befb4#32, 0x11e2923e#32, 0xcf51e923#32, 0x8e188f6f#32
  ]

def final_state : ArmState := aes_hw_set_encrypt_key_test 167 key_bits
def final_rd_key : BitVec 1408 := read_mem_bytes 176 key_address final_state
def final_rounds : BitVec 64 := read_mem_bytes 8 (key_address + 240) final_state

example : read_err final_state = StateError.None := by native_decide
example : final_rd_key = revflat rd_key := by native_decide
example : final_rounds = rounds := by native_decide

end AES128

namespace AES192

def key_bits : BitVec 64 := 192#64
def rounds : BitVec 64 := 12#64
def rd_key : List (BitVec 32) :=
  [ 0x00#32, 0x00#32, 0x00#32, 0x00#32,
    0x00#32, 0x00#32, 0x63636362#32, 0x63636362#32,
    0x63636362#32, 0x63636362#32, 0x63636362#32, 0x63636362#32,
    0xc998989b#32, 0xaafbfbf9#32, 0xc998989b#32, 0xaafbfbf9#32,
    0xc998989b#32, 0xaafbfbf9#32, 0x50349790#32, 0xfacf6c69#32,
    0x3357f4f2#32, 0x99ac0f0b#32, 0x50349790#32, 0xfacf6c69#32,
    0xa9191dc8#32, 0x53d671a1#32, 0x60818553#32, 0xf92d8a58#32,
    0xa9191dc8#32, 0x53d671a1#32, 0x9bf4eb7b#32, 0xc8229ada#32,
    0xa8a31f89#32, 0x518e95d1#32, 0xf8978819#32, 0xab41f9b8#32,
    0xf79668c2#32, 0x3fb4f218#32, 0x9717ed91#32, 0xc6997840#32,
    0x3e0ef059#32, 0x954f09e1#32, 0xfbcec83#32, 0x30081e9b#32,
    0xa71ff30a#32, 0x61868b4a#32, 0x5f887b13#32, 0xcac772f2#32,
    0x86c82a43#32, 0xb6c034d8#32, 0x11dfc7d2#32, 0x70594c98#32
  ]

def final_state : ArmState := aes_hw_set_encrypt_key_test 195 key_bits
def final_rd_key : BitVec 1664 := read_mem_bytes 208 key_address final_state
def final_rounds : BitVec 64 := read_mem_bytes 8 (key_address + 240) final_state

example : read_err final_state = StateError.None := by native_decide
example : final_rd_key = revflat rd_key := by native_decide
example : final_rounds = rounds := by native_decide

end AES192

namespace AES256

def key_bits : BitVec 64 := 256#64
def rounds : BitVec 64 := 14#64
def rd_key : List (BitVec 32) :=
  [ 0x00#32, 0x00#32, 0x00#32, 0x00#32,
    0x00#32, 0x00#32, 0x00#32, 0x00#32,
    0x63636362#32, 0x63636362#32, 0x63636362#32, 0x63636362#32,
    0xfbfbfbaa#32, 0xfbfbfbaa#32, 0xfbfbfbaa#32, 0xfbfbfbaa#32,
    0xcf6c6c6f#32, 0xac0f0f0d#32, 0xcf6c6c6f#32, 0xac0f0f0d#32,
    0x6a8d8d7d#32, 0x917676d7#32, 0x6a8d8d7d#32, 0x917676d7#32,
    0xc1ed5453#32, 0x6de25b5e#32, 0xa28e3731#32, 0xe81383c#32,
    0xc1818a96#32, 0x50f7fc41#32, 0x3a7a713c#32, 0xab0c07eb#32,
    0x288faa9e#32, 0x456df1c0#32, 0xe7e3c6f1#32, 0xe962fecd#32,
    0xdf2b312b#32, 0x8fdccd6a#32, 0xb5a6bc56#32, 0x1eaabbbd#32,
    0x52fd0664#32, 0x1790f7a4#32, 0xf0733155#32, 0x1911cf98#32,
    0xba9bb6d#32, 0x84757607#32, 0x31d3ca51#32, 0x2f7971ec#32,
    0x9ce8b0e7#32, 0x8b784743#32, 0x7b0b7616#32, 0x621ab98e#32,
    0xa10bed74#32, 0x257e9b73#32, 0x14ad5122#32, 0x3bd420ce#32,
    0x170af810#32, 0x9c72bf53#32, 0xe779c945#32, 0x856370cb#32
 ]

def final_state : ArmState := aes_hw_set_encrypt_key_test 198 key_bits
def final_rd_key : BitVec 1920 := read_mem_bytes 240 key_address final_state
def final_rounds : BitVec 64 := read_mem_bytes 8 (key_address + 240) final_state

example : read_err final_state = StateError.None := by native_decide
example : final_rd_key = revflat rd_key := by native_decide
example : final_rounds = rounds := by native_decide

end AES256

end AESHWSetEncryptKeyProgramTest

namespace AESHWEncryptProgramTest

def in_address : BitVec 64 := 0#64
def key_address : BitVec 64 := 16#64
def out_address : BitVec 64 := in_address

def aes_hw_encrypt_test (n : Nat) (in_block : BitVec 128)
  (rounds : BitVec 64) (key_schedule : BitVec ((rounds.toNat + 1) * 16 * 8)) : ArmState :=
  let init_gpr : Store (BitVec 5) (BitVec 64) :=
    fun i =>
      match i with
        | 0 => in_address
        | 1 => out_address
        | 2 => key_address
        | _ => 0#64
    let s := { gpr := init_gpr,
               sfp := (fun (_ : BitVec 5) => 0#128),
               pc := 0x79f5a0#64,
               pstate := PState.zero,
               mem := (fun (_ :BitVec 64) => 0#8),
               program := AESHWEncryptProgram.aes_hw_encrypt_program,
               error := StateError.None
             }
  -- write in_block
  let s := write_mem_bytes 16 in_address in_block s
  -- write kKey
  let s := write_mem_bytes ((rounds.toNat+1)*16) key_address key_schedule s
  -- write rounds
  let s := write_mem_bytes 8 (key_address + 240) rounds s
  let final_state := run n s
  final_state

namespace AES128

def in_block : List (BitVec 8) := List.replicate 16 0x00#8

def key_schedule : List (BitVec 32) := AESHWSetEncryptKeyProgramTest.AES128.rd_key
def rounds : BitVec 64 := 10

def out_block : List (BitVec 8) :=
  [ 0x66#8, 0xe9#8, 0x4b#8, 0xd4#8, 0xef#8, 0x8a#8, 0x2c#8, 0x3b#8,
    0x88#8, 0x4c#8, 0xfa#8, 0x59#8, 0xca#8, 0x34#8, 0x2b#8, 0x2e#8
  ]

def final_state : ArmState :=
  aes_hw_encrypt_test 44 (revflat in_block) rounds (revflat key_schedule)
def final_ciphertext : BitVec 128 := read_mem_bytes 16 out_address final_state

example : read_err final_state = StateError.None := by native_decide
example : final_ciphertext = revflat out_block := by native_decide

end AES128



namespace AES192

def in_block : List (BitVec 8) := List.replicate 16 0x00#8

def key_schedule : List (BitVec 32) := AESHWSetEncryptKeyProgramTest.AES192.rd_key
def rounds : BitVec 64 := 12

def out_block : List (BitVec 8) :=
  [ 0xaa#8, 0xe0#8, 0x69#8, 0x92#8, 0xac#8, 0xbf#8, 0x52#8, 0xa3#8,
    0xe8#8, 0xf4#8, 0xa9#8, 0x6e#8, 0xc9#8, 0x30#8, 0x0b#8, 0xd7#8
  ]

def final_state : ArmState :=
  aes_hw_encrypt_test 52 (revflat in_block) rounds (revflat key_schedule)
def final_ciphertext : BitVec 128 := read_mem_bytes 16 out_address final_state

example : read_err final_state = StateError.None := by native_decide
example : final_ciphertext = revflat out_block := by native_decide


end AES192

namespace AES256

def in_block : List (BitVec 8) := List.replicate 16 0x00#8

def key_schedule : List (BitVec 32) := AESHWSetEncryptKeyProgramTest.AES256.rd_key
def rounds : BitVec 64 := 14

def out_block : List (BitVec 8) :=
  [ 0xdc#8, 0x95#8, 0xc0#8, 0x78#8, 0xa2#8, 0x40#8, 0x89#8, 0x89#8,
    0xad#8, 0x48#8, 0xa2#8, 0x14#8, 0x92#8, 0x84#8, 0x20#8, 0x87#8
  ]

def final_state : ArmState :=
  aes_hw_encrypt_test 60 (revflat in_block) rounds (revflat key_schedule)
def final_ciphertext : BitVec 128 := read_mem_bytes 16 out_address final_state

example : read_err final_state = StateError.None := by native_decide
example : final_ciphertext = revflat out_block := by native_decide


end AES256

end AESHWEncryptProgramTest

namespace AESHWCtr32EncryptBlocksProgramTest

def in_address : BitVec 64 := 0#64
def key_address : BitVec 64 := 80#64 -- assuming maximum 5 blocks covering 0, 1, 2, 3, 4, 5
def round_address : BitVec 64 := key_address + 240
def out_address : BitVec 64 := in_address
def ivec_address : BitVec 64 := 328#64

def aes_hw_ctr32_encrypt_blocks_test (n : Nat)
  (len : BitVec 64) (in_block : List (BitVec 8))
  (rounds : BitVec 64) (key_schedule : List (BitVec 32))
  (ivec : BitVec 128)
  : ArmState :=
  let init_gpr : Store (BitVec 5) (BitVec 64) :=
    fun i =>
      match i with
        | 0 => in_address
        | 1 => out_address
        | 2 => len
        | 3 => key_address
        | 4 => ivec_address
        | _ => 0#64
    let s := { gpr := init_gpr,
               sfp := (fun (_ : BitVec 5) => 0#128),
               pc := 0x79f8a0#64,
               pstate := PState.zero,
               mem := (fun (_ :BitVec 64) => 0#8),
               program := AESHWCtr32EncryptBlocksProgram.aes_hw_ctr32_encrypt_blocks_program,
               error := StateError.None
             }
  -- write in_block
  have h1 : 8 * in_block.length = in_block.length * 8 := by omega
  let s := write_mem_bytes in_block.length in_address (BitVec.cast h1 (revflat in_block)) s
  -- write key_schedule
  have h2 : 32 * key_schedule.length = 4 * key_schedule.length * 8 := by omega
  let s := write_mem_bytes (4 * key_schedule.length) key_address (BitVec.cast h2 (revflat key_schedule)) s
  -- write rounds
  let s := write_mem_bytes 8 round_address rounds s
  -- write ivec
  let s := write_mem_bytes 16 ivec_address ivec s
  let final_state := run n s
  final_state

def in_block : List (BitVec 8) := List.replicate 80 0x00#8

def ivec : BitVec 128 := 0x0#128

-- len = 0, 1, 2, 3, 4, 5
-- Note: aes_hw_ctr32_encrypt_blocks will encrypt two blocks when len = 0, why?
-- Suspicion is that this function is never called with len = 0
namespace AES128Ctr32

def rounds : BitVec 64 := 10
def key_schedule : List (BitVec 32) := AESHWSetEncryptKeyProgramTest.AES128.rd_key
def buf_res_128 : List (BitVec 8) :=
  [ 0x66#8, 0xe9#8, 0x4b#8, 0xd4#8, 0xef#8, 0x8a#8, 0x2c#8, 0x3b#8,
    0x88#8, 0x4c#8, 0xfa#8, 0x59#8, 0xca#8, 0x34#8, 0x2b#8, 0x2e#8,
    0x58#8, 0xe2#8, 0xfc#8, 0xce#8, 0xfa#8, 0x7e#8, 0x30#8, 0x61#8,
    0x36#8, 0x7f#8, 0x1d#8, 0x57#8, 0xa4#8, 0xe7#8, 0x45#8, 0x5a#8,
    0x03#8, 0x88#8, 0xda#8, 0xce#8, 0x60#8, 0xb6#8, 0xa3#8, 0x92#8,
    0xf3#8, 0x28#8, 0xc2#8, 0xb9#8, 0x71#8, 0xb2#8, 0xfe#8, 0x78#8,
    0xf7#8, 0x95#8, 0xaa#8, 0xab#8, 0x49#8, 0x4b#8, 0x59#8, 0x23#8,
    0xf7#8, 0xfd#8, 0x89#8, 0xff#8, 0x94#8, 0x8b#8, 0xc1#8, 0xe0#8,
    0x20#8, 0x02#8, 0x11#8, 0x21#8, 0x4e#8, 0x73#8, 0x94#8, 0xda#8,
    0x20#8, 0x89#8, 0xb6#8, 0xac#8, 0xd0#8, 0x93#8, 0xab#8, 0xe0#8
  ]

-- len = 0
def final_state0 : ArmState :=
  aes_hw_ctr32_encrypt_blocks_test 83 0 in_block rounds key_schedule ivec
def final_buf0 : BitVec 640 := read_mem_bytes 80 out_address final_state0
example : read_err final_state0 = StateError.None := by native_decide
example: final_buf0 = (BitVec.zero 384) ++ (extractLsb 255 0 (revflat buf_res_128)) := by native_decide

-- len = 1
def final_state1 : ArmState :=
  aes_hw_ctr32_encrypt_blocks_test 82 1 in_block rounds key_schedule ivec
def final_buf1 : BitVec 640 := read_mem_bytes 80 out_address final_state1
example : read_err final_state1 = StateError.None := by native_decide
example: final_buf1 = (BitVec.zero 512) ++ (extractLsb 127 0 (revflat buf_res_128)) := by native_decide

-- -- len = 2
def final_state2 : ArmState :=
  aes_hw_ctr32_encrypt_blocks_test 82 2 in_block rounds key_schedule ivec
def final_buf2 : BitVec 640 := read_mem_bytes 80 out_address final_state2
example : read_err final_state2 = StateError.None := by native_decide
example: final_buf2 = (BitVec.zero 384) ++ (extractLsb 255 0 (revflat buf_res_128)) := by native_decide

-- len = 3
def final_state3 : ArmState :=
  aes_hw_ctr32_encrypt_blocks_test 129 3 in_block rounds key_schedule ivec
def final_buf3 : BitVec 640 := read_mem_bytes 80 out_address final_state3
example : read_err final_state3 = StateError.None := by native_decide
example: final_buf3 = (BitVec.zero 256) ++ (extractLsb 383 0 (revflat buf_res_128)) := by native_decide

-- len = 4
def final_state4 : ArmState :=
  aes_hw_ctr32_encrypt_blocks_test 187 4 in_block rounds key_schedule ivec
def final_buf4 : BitVec 640 := read_mem_bytes 80 out_address final_state4
example : read_err final_state4 = StateError.None := by native_decide
example: final_buf4 = (BitVec.zero 127) ++ (extractLsb 512 0 (revflat buf_res_128)) := by native_decide

-- len = 5
def final_state5 : ArmState :=
  aes_hw_ctr32_encrypt_blocks_test 188 5 in_block rounds key_schedule ivec
def final_buf5 : BitVec 640 := read_mem_bytes 80 out_address final_state5
example : read_err final_state5 = StateError.None := by native_decide
example: final_buf5 = revflat buf_res_128 := by native_decide

end AES128Ctr32

namespace AES192Ctr32

def rounds : BitVec 64 := 12
def key_schedule : List (BitVec 32) := AESHWSetEncryptKeyProgramTest.AES192.rd_key
def buf_res_192 : List (BitVec 8) :=
  [ 0xaa#8, 0xe0#8, 0x69#8, 0x92#8, 0xac#8, 0xbf#8, 0x52#8, 0xa3#8,
    0xe8#8, 0xf4#8, 0xa9#8, 0x6e#8, 0xc9#8, 0x30#8, 0x0b#8, 0xd7#8,
    0xcd#8, 0x33#8, 0xb2#8, 0x8a#8, 0xc7#8, 0x73#8, 0xf7#8, 0x4b#8,
    0xa0#8, 0x0e#8, 0xd1#8, 0xf3#8, 0x12#8, 0x57#8, 0x24#8, 0x35#8,
    0x98#8, 0xe7#8, 0x24#8, 0x7c#8, 0x07#8, 0xf0#8, 0xfe#8, 0x41#8,
    0x1c#8, 0x26#8, 0x7e#8, 0x43#8, 0x84#8, 0xb0#8, 0xf6#8, 0x00#8,
    0x2a#8, 0x34#8, 0x93#8, 0xe6#8, 0x62#8, 0x35#8, 0xee#8, 0x67#8,
    0xde#8, 0xec#8, 0xcd#8, 0x2f#8, 0x3b#8, 0x39#8, 0x3b#8, 0xd8#8,
    0xfd#8, 0xaa#8, 0x17#8, 0xc2#8, 0xcd#8, 0xe2#8, 0x02#8, 0x68#8,
    0xfe#8, 0x36#8, 0xe1#8, 0x64#8, 0xea#8, 0x53#8, 0x21#8, 0x51#8
  ]

-- len = 5
def final_state : ArmState :=
  aes_hw_ctr32_encrypt_blocks_test 216 5 in_block rounds key_schedule ivec
def final_buf : BitVec 640 := read_mem_bytes 80 out_address final_state
example : read_err final_state = StateError.None := by native_decide
example: final_buf = revflat buf_res_192 := by native_decide

end AES192Ctr32

namespace AES256Ctr32

def rounds : BitVec 64 := 14
def key_schedule : List (BitVec 32) := AESHWSetEncryptKeyProgramTest.AES256.rd_key
def buf_res_256 : List (BitVec 8) :=
  [ 0xdc#8, 0x95#8, 0xc0#8, 0x78#8, 0xa2#8, 0x40#8, 0x89#8, 0x89#8,
    0xad#8, 0x48#8, 0xa2#8, 0x14#8, 0x92#8, 0x84#8, 0x20#8, 0x87#8,
    0x53#8, 0x0f#8, 0x8a#8, 0xfb#8, 0xc7#8, 0x45#8, 0x36#8, 0xb9#8,
    0xa9#8, 0x63#8, 0xb4#8, 0xf1#8, 0xc4#8, 0xcb#8, 0x73#8, 0x8b#8,
    0xce#8, 0xa7#8, 0x40#8, 0x3d#8, 0x4d#8, 0x60#8, 0x6b#8, 0x6e#8,
    0x07#8, 0x4e#8, 0xc5#8, 0xd3#8, 0xba#8, 0xf3#8, 0x9d#8, 0x18#8,
    0x72#8, 0x60#8, 0x03#8, 0xca#8, 0x37#8, 0xa6#8, 0x2a#8, 0x74#8,
    0xd1#8, 0xa2#8, 0xf5#8, 0x8e#8, 0x75#8, 0x06#8, 0x35#8, 0x8e#8,
    0xdd#8, 0x4a#8, 0xb1#8, 0x28#8, 0x4d#8, 0x4a#8, 0xe1#8, 0x7b#8,
    0x41#8, 0xe8#8, 0x59#8, 0x24#8, 0x47#8, 0x0c#8, 0x36#8, 0xf7#8
  ]

-- len = 5
def final_state : ArmState :=
  aes_hw_ctr32_encrypt_blocks_test 244 5 in_block rounds key_schedule ivec
def final_buf : BitVec 640 := read_mem_bytes 80 out_address final_state
example : read_err final_state = StateError.None := by native_decide
example: final_buf = revflat buf_res_256 := by native_decide

end AES256Ctr32


end AESHWCtr32EncryptBlocksProgramTest
