/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.BitVec
import Arm.Exec
import Arm.Cfg.Cfg
import Tests.Common
import Tests.«AES-GCM».AESGCMEncKernelProgram
import Tests.«AES-GCM».AESGCMDecKernelProgram

open BitVec

-- Tests are taken from AWS-LC's ABI tests (GCMTest.ABI) for these assembly routines

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

namespace AESGCMEncDecKernelProgramTest

def in_bits : BitVec 64 := 4096#64

def in_address : BitVec 64 := 0#64
def out_address : BitVec 64 := in_address
def Xi_address : BitVec 64 := in_bits.toNat/8
def ivec_address : BitVec 64 := Xi_address.toNat + 16
def key_address : BitVec 64 := ivec_address + 16
def Htable_address : BitVec 64 := key_address + 240 + 8

def in_blocks : List (BitVec 8) := List.replicate 512 0x2a#8
def ivec : List (BitVec 8) := List.replicate 16 0x00#8

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

def ivec_res : List (BitVec 8) :=
  [ 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
    0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x20#8 ]

def aes_gcm_enc_kernel_test (n : Nat) (plain_blocks : BitVec 4096)
  (Xi : BitVec 128) (Htable : BitVec 2048) (rounds : BitVec 64)
  (keys : BitVec ((rounds.toNat + 1) * 16 * 8)) (ivec : BitVec 128)
  : ArmState :=
  let init_gpr : Store (BitVec 5) (BitVec 64) :=
    fun i =>
      match i with
        | 0 => in_address
        | 1 => in_bits
        | 2 => out_address
        | 3 => Xi_address
        | 4 => ivec_address
        | 5 => key_address
        | 6 => Htable_address
        | _ => 0#64
  let s := { gpr := init_gpr,
             sfp := (fun (_ : BitVec 5) => 0#128),
             pc := 0x7a0cf0#64,
             pstate := zero_pstate,
             mem := (fun (_ :BitVec 64) => 0#8),
             program := AESGCMEncKernelProgram.aes_gcm_enc_kernel_program,
             error := StateError.None
           }
  -- write in_blocks
  let s := write_mem_bytes 512 in_address plain_blocks s
  -- write Xi
  let s := write_mem_bytes 16 Xi_address Xi s
  -- write Htable
  let s := write_mem_bytes 256 Htable_address Htable s
  -- write key schedule
  let s := write_mem_bytes ((rounds.toNat + 1) * 16) key_address keys s
  -- write rounds
  let s := write_mem_bytes 8 (key_address + 240) rounds s
  -- write ivec
  let s := write_mem_bytes 16 ivec_address ivec s
  let final_state := run n s
  final_state

def aes_gcm_dec_kernel_test (n : Nat) (cipher_blocks : BitVec 4096)
  (Xi : BitVec 128) (Htable : BitVec 2048) (rounds : BitVec 64)
  (keys : BitVec ((rounds.toNat + 1) * 16 * 8)) (ivec : BitVec 128)
  : ArmState :=
  let init_gpr : Store (BitVec 5) (BitVec 64) :=
    fun i =>
      match i with
        | 0 => in_address
        | 1 => in_bits
        | 2 => out_address
        | 3 => Xi_address
        | 4 => ivec_address
        | 5 => key_address
        | 6 => Htable_address
        | _ => 0#64
  let s := { gpr := init_gpr,
             sfp := (fun (_ : BitVec 5) => 0#128),
             pc := 0x7a1880#64,
             pstate := zero_pstate,
             mem := (fun (_ :BitVec 64) => 0#8),
             program := AESGCMDecKernelProgram.aes_gcm_dec_kernel_program,
             error := StateError.None
           }
  -- write in_blocks
  let s := write_mem_bytes 512 in_address cipher_blocks s
  -- write Xi
  let s := write_mem_bytes 16 Xi_address Xi s
  -- write Htable
  let s := write_mem_bytes 256 Htable_address Htable s
  -- write key schedule
  let s := write_mem_bytes ((rounds.toNat + 1) * 16) key_address keys s
  -- write rounds
  let s := write_mem_bytes 8 (key_address + 240) rounds s
  -- write ivec
  let s := write_mem_bytes 16 ivec_address ivec s
  let final_state := run n s
  final_state

namespace AES_128_GCM

def Xi : List (BitVec 8) :=
  [ 0xa1#8, 0xdc#8, 0x0c#8, 0x34#8, 0x1c#8, 0x8e#8, 0x58#8, 0xd8#8,
    0x48#8, 0x15#8, 0x9c#8, 0x20#8, 0x8b#8, 0x91#8, 0xcb#8, 0xf4#8 ]
def key : List (BitVec 32) :=
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
def rounds : BitVec 64 := 10
-- Note: ciphertext should be of type List (BitVec 8), using BitVec 64 to avoid long list
def ciphertext : List (BitVec 64) :=
  [ 0x1106a0c5fe61c34c#64, 0x4011ee073d066a2#64,
    0x4b1a54d0e4d6c872#64, 0x706fcd8e7d37551c#64,
    0xb8899c4ae4f0a229#64, 0x52d4985b93e802d9#64,
    0x97361638180bfdd#64, 0xcaeba1bed5a3d7dd#64,
    0xf0be59640b3b280a#64, 0xca81b9fa869ca30a#64,
    0x5703a43b338867e3#64, 0xd8a2e9e396965451#64,
    0x4b1fc482af57f4a0#64, 0xbb280dff830e5b45#64,
    0xd5baecbc316792bf#64, 0xcaa3c6d821c90705#64,
    0xda2e4f3844527928#64, 0xf40b2989622693f0#64,
    0xb456346c9acc6f19#64, 0x6a15c2f7d4504146#64,
    0xa5d7d2be4dd099f4#64, 0xd842b7f0e1a7827f#64,
    0x542d0a1ee2e35639#64, 0xda27414398a0d856#64,
    0x807a8672016f3b77#64, 0xcfad319cbf8b9904#64,
    0x6a82ddfdff4770ec#64, 0x225948de558bff4f#64,
    0x938e159c4763284a#64, 0xbf2629895512c431#64,
    0x75bbca1d2ea7158d#64, 0x2081a7078cfdcf96#64,
    0x28f494ea31699872#64, 0x52c643a3096a257f#64,
    0x61becce7d6943a2e#64, 0xb7b0c9c1572af743#64,
    0xde978e33df0e7496#64, 0x75384d21c6f39b52#64,
    0x6b53778fd0449a02#64, 0xe9e9a37afe02fc00#64,
    0xe7dc37889967d32e#64, 0x6b7e1f1104044785#64,
    0x78cd0d2ff360dcc5#64, 0x262d8bfa9ec1988e#64,
    0x56f1050d04b2c8c8#64, 0x7dd38abf9aae9fde#64,
    0x57c91dbe420292d7#64, 0xecd9ec53f900a1ee#64,
    0x4fa692855dc47dc3#64, 0x2e86fc6048bb1be#64,
    0xabc400ce50bace4f#64, 0xe8cec8bbf586b212#64,
    0x9c01f45c20a4a837#64, 0x4b35c574b4ac4591#64,
    0xb001ab485ff8c7a7#64, 0xd9071f7640b3c23e#64,
    0xb03b0ac6fc4a54ab#64, 0x87c33c64b20e278#64,
    0x7be0c6070b6a5848#64, 0x53721e0d149cc075#64,
    0xd4760af48d1c8262#64, 0x3ba11e361fa2e8ea#64,
    0x5abef34920f76b53#64, 0xb2e426e60f34914#64 ]

def Xi_res : List (BitVec 8) :=
  [ 0x7f#8, 0x83#8, 0x64#8, 0xd9#8, 0x05#8, 0xfc#8, 0x76#8, 0x0b#8,
    0x58#8, 0xe2#8, 0xdb#8, 0xa2#8, 0x34#8, 0x0a#8, 0x38#8, 0x5d#8 ]

namespace enc

-- AES_128_GCM encrypt test
def final_state : ArmState :=
  have h : 8 * in_blocks.length = 4096 := by
    unfold in_blocks
    simp only [List.length_replicate]
  aes_gcm_enc_kernel_test 1514 (BitVec.cast h $ revflat in_blocks) (revflat Xi) (revflat Htable)
    rounds (revflat key) (revflat ivec)

def final_ciphertext : BitVec 4096 := read_mem_bytes 512 out_address final_state
def final_hash : BitVec 128 := read_mem_bytes 16 Xi_address final_state
def final_ivec : BitVec 128 := read_mem_bytes 16 ivec_address final_state

example : read_err final_state = StateError.None := by native_decide
example : final_hash = revflat Xi_res := by native_decide
example : final_ciphertext = revflat ciphertext := by native_decide
example : final_ivec = revflat ivec_res := by native_decide

end enc

namespace dec

-- AES_128_GCM decrypt test
def final_state : ArmState :=
  aes_gcm_dec_kernel_test 1519 (revflat ciphertext) (revflat Xi) (revflat Htable)
    rounds (revflat key) (revflat ivec)

def final_ciphertext : BitVec 4096 := read_mem_bytes 512 out_address final_state
def final_hash : BitVec 128 := read_mem_bytes 16 Xi_address final_state
def final_ivec : BitVec 128 := read_mem_bytes 16 ivec_address final_state

example : read_err final_state = StateError.None := by native_decide
example : final_hash = revflat Xi_res := by native_decide
set_option maxRecDepth 2100 in
example : final_ciphertext = revflat in_blocks := by native_decide
example : final_ivec = revflat ivec_res := by native_decide

end dec

end AES_128_GCM

namespace AES_192_GCM

def Xi : List (BitVec 8) :=
  [ 0x96#8, 0xfd#8, 0x56#8, 0x3e#8, 0x10#8, 0x56#8, 0x2a#8, 0x62#8,
    0x10#8, 0xa3#8, 0x75#8, 0x8d#8, 0xdb#8, 0x2f#8, 0x40#8, 0xee#8 ]
def key : List (BitVec 32) :=
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
def rounds : BitVec 64 := 12
-- Note: ciphertext should be of type List (BitVec 8), using BitVec 64 to avoid long list
def ciphertext : List (BitVec 64) :=
  [ 0x89789586b843ca80#64, 0xfd211ae34483dec2#64,
    0x61dd59eda09819e7#64, 0x1f0e7d38d9fb248a#64,
    0x6bd4da2d560ecdb2#64, 0x2adc9aae69540c36#64,
    0x4dc41f48ccb91e00#64, 0xf211131105e7c6f4#64,
    0x4228c8e7e83d80d7#64, 0x7b0b79c04ecb1cd4#64,
    0x2ec2589c0ef470f8#64, 0x36271936686da728#64,
    0xf5a7fe8f275d3e06#64, 0x3bf98a8c6ff912df#64,
    0x502a48391c84a522#64, 0xe3ce2b75f6e23566#64,
    0xb210269ce700886d#64, 0x191ec0fac65ca540#64,
    0xed4079eb00ff9f88#64, 0x6b2918cf6d3cf508#64,
    0xef7d6f7f1ed47371#64, 0x3427cf69d42acd13#64,
    0xce6ded0ed726bb3d#64, 0x900e81c0b8e9e69c#64,
    0xf11d6fcbec16fe11#64, 0xbf5d837153f69b78#64,
    0x1e9ad58454f2c097#64, 0x9a77fa0dcd9e9b2c#64,
    0x6fd332f3cc153e00#64, 0x473797b469316e1#64,
    0x8b482374a6dbce7a#64, 0x2f49fd7f459087d6#64,
    0x21995659f8bd8c07#64, 0x449636d06e6c605e#64,
    0x943ea11ef24c0c64#64, 0xf33f3981cb0cdc02#64,
    0x358616c6030f1eba#64, 0x94360924e243ae6f#64,
    0x5c585afd366baad4#64, 0xe7d66e5570f2b106#64,
    0x7ea28af2e4226dcb#64, 0xe96dfa767a3649b9#64,
    0xd3fd90d1c36fe3de#64, 0x90364a09165a2a2a#64,
    0x4738f725eb3760f5#64, 0xb7a1f663e79618ee#64,
    0x4c9d4e56bfeec341#64, 0xcc0ce920ca547ebd#64,
    0xc88129ab75156c0c#64, 0xa8cb289b9fabf9f4#64,
    0x96a6492c96a6a4cb#64, 0xb1b1bb7016ca852c#64,
    0xe410a1efc7049bd7#64, 0x1c15ad8197b0e694#64,
    0xa7c4c1fb82a88e13#64, 0x48e7d2d8b31c90d4#64,
    0x6b79453a346e7bb3#64, 0x15b9b51658ae79ae#64,
    0x5b36d00ec734a377#64, 0x62d86b824ad11ab6#64,
    0x154ac4dc2af2cd48#64, 0x1fd559984b124cc8#64,
    0x800b84a1f67dcc48#64, 0xdac18880a5237fb2#64 ]
def Xi_res : List (BitVec 8) :=
  [ 0x51#8, 0xec#8, 0x5b#8, 0xb9#8, 0x6b#8, 0x0f#8, 0xa2#8, 0x02#8,
    0x80#8, 0x02#8, 0x19#8, 0x33#8, 0xf4#8, 0xe3#8, 0x8e#8, 0x0e#8 ]

namespace enc

-- AES_192_GCM encrypt test
def final_state : ArmState :=
  have h : 8 * in_blocks.length = 4096 := by
    unfold in_blocks
    simp only [List.length_replicate]
  aes_gcm_enc_kernel_test 1650 (BitVec.cast h $ revflat in_blocks) (revflat Xi) (revflat Htable)
    rounds (revflat key) (revflat ivec)

def final_ciphertext : BitVec 4096 := read_mem_bytes 512 out_address final_state
def final_hash : BitVec 128 := read_mem_bytes 16 Xi_address final_state
def final_ivec : BitVec 128 := read_mem_bytes 16 ivec_address final_state

example : read_err final_state = StateError.None := by native_decide
example : final_hash = revflat Xi_res := by native_decide
example : final_ciphertext = (revflat ciphertext) := by native_decide
example : final_ivec = (revflat ivec_res) := by native_decide

end enc

namespace dec

-- AES_192_GCM decrypt test
def final_state : ArmState :=
  aes_gcm_dec_kernel_test 1655 (revflat ciphertext) (revflat Xi) (revflat Htable)
    rounds (revflat key) (revflat ivec)

def final_ciphertext : BitVec 4096 := read_mem_bytes 512 out_address final_state
def final_hash : BitVec 128 := read_mem_bytes 16 Xi_address final_state
def final_ivec : BitVec 128 := read_mem_bytes 16 ivec_address final_state

example : read_err final_state = StateError.None := by native_decide
example : final_hash = revflat Xi_res := by native_decide
set_option maxRecDepth 2100 in
example : final_ciphertext = revflat in_blocks := by native_decide
example : final_ivec = revflat ivec_res := by native_decide

end dec

end AES_192_GCM

namespace AES_256_GCM

def Xi : List (BitVec 8) :=
  [ 0x72#8, 0xde#8, 0x99#8, 0x1c#8, 0x84#8, 0xa4#8, 0x76#8, 0xab#8,
    0x5e#8, 0x87#8, 0xe1#8, 0x3c#8, 0x51#8, 0x7b#8, 0xf8#8, 0x9e#8 ]
def key : List (BitVec 32) :=
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
def rounds : BitVec 64 := 14
-- Note: ciphertext should be of type List (BitVec 8), using BitVec 64 to avoid long list
def ciphertext : List (BitVec 64) :=
  [ 0xa3a36a8852eabff6#64, 0xad0aaeb83e886287#64,
    0x931c6fedd1a02579#64, 0xa159e1eedb9e4983#64,
    0x44414a67176a8de4#64, 0x32b7d990f9ef642d#64,
    0x5e008c1de0294a58#64, 0xa41f2c5fa4df88fb#64,
    0x51cb6067029b60f7#64, 0xdd1c266d0e73c26b#64,
    0x1a5591abcbe16b6d#64, 0x35102681c937564b#64,
    0x1d07820b59a5eefa#64, 0x8a4dbb6bca86bf4a#64,
    0x78ce4ea9a638596#64, 0x8737747e4c3696cc#64,
    0xef0af44e75dd081#64, 0x3d606cfef979a75#64,
    0xd9ca1d0281cb2090#64, 0x384a3db9249dad49#64,
    0x9bdef24c91e84869#64, 0xacf9b6061ec2d61d#64,
    0x824258c8bc683e8b#64, 0x53ff2f821ddf27cf#64,
    0x1ec77dd997c10b91#64, 0xe0f77a5ba99f7295#64,
    0x5a4a2048740848d9#64, 0x4c0e78d103df7486#64,
    0x34cf7e61ea52a15c#64, 0xec75892ccf2dd0df#64,
    0xcb0cacb60e3a9d9a#64, 0x494fd0252ff4083#64,
    0x9769c456708aba3e#64, 0xc2bf623c97ca1c3#64,
    0xed95eba844f5fc64#64, 0x1eceea8379877300#64,
    0x8d6a537a52784657#64, 0x34859cc2b990dcf4#64,
    0x4ced314b5c58796c#64, 0x6d82311a577276bf#64,
    0x6a469a08df7e386#64, 0xf958665e3eff4320#64,
    0xac68d954b1411865#64, 0x9444cac08dd224e0#64,
    0xe1076a385879b64c#64, 0x8ddeed5cb7c3c075#64,
    0x128ad027b69d9740#64, 0xa1fe24590602c88a#64,
    0x14e5a43c0586b7ac#64, 0xa4067b8635cc3a8c#64,
    0x5c9648f42ca6d1bf#64, 0x66acf1a01f7b7f43#64,
    0x8099b09e3ed342e8#64, 0xab5358fb98d7c70a#64,
    0x85ffbf7f2999e1d#64, 0xb5e56df6ce9506c1#64,
    0x7cf1f409e736d09a#64, 0xcdf4c7ce20dffbb9#64,
    0x2259caecdd9a0a22#64, 0x18469abdd73707b4#64,
    0x1e956702f21c2a8f#64, 0x56e2049cca040342#64,
    0xa4d9e5cc19b56a2#64, 0xad49bcdbf11a6b3a#64
  ]
def Xi_res : List (BitVec 8) :=
  [ 0x8d#8, 0x07#8, 0xee#8, 0x6f#8, 0x96#8, 0xa3#8, 0xb5#8, 0x80#8,
    0xf9#8, 0xd1#8, 0x51#8, 0xa5#8, 0xf1#8, 0x5c#8, 0xb7#8, 0x26#8 ]

namespace enc

-- AES_256_GCM encrypt test
def final_state : ArmState :=
  have h : 8 * in_blocks.length = 4096 := by
    unfold in_blocks
    simp only [List.length_replicate]
  aes_gcm_enc_kernel_test 1778 (BitVec.cast h $ revflat in_blocks) (revflat Xi) (revflat Htable)
    rounds (revflat key) (revflat ivec)

def final_ciphertext : BitVec 4096 := read_mem_bytes 512 out_address final_state
def final_hash : BitVec 128 := read_mem_bytes 16 Xi_address final_state
def final_ivec : BitVec 128 := read_mem_bytes 16 ivec_address final_state

example : read_err final_state = StateError.None := by native_decide
example : final_hash = revflat Xi_res := by native_decide
example : final_ciphertext = revflat ciphertext := by native_decide
example : final_ivec = (revflat ivec_res) := by native_decide

end enc

namespace dec

-- AES_256_GCM decrypt test
def final_state : ArmState :=
  aes_gcm_dec_kernel_test 1783 (revflat ciphertext) (revflat Xi) (revflat Htable)
    rounds (revflat key) (revflat ivec)

def final_ciphertext : BitVec 4096 := read_mem_bytes 512 out_address final_state
def final_hash : BitVec 128 := read_mem_bytes 16 Xi_address final_state
def final_ivec : BitVec 128 := read_mem_bytes 16 ivec_address final_state

example : read_err final_state = StateError.None := by native_decide
example : final_hash = revflat Xi_res := by native_decide
set_option maxRecDepth 2100 in
example : final_ciphertext = revflat in_blocks := by native_decide
example : final_ivec = revflat ivec_res := by native_decide

end dec

end AES_256_GCM

end AESGCMEncDecKernelProgramTest
