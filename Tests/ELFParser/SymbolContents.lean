/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import ELFSage
import Arm.State

/- Given a file path, get the raw ELF file. -/
def getELFFile (elfFile : System.FilePath) : IO RawELFFile := do
  let bytes ← IO.FS.readBinFile elfFile
  match mkRawELFFile? bytes with
  | .error warn => throw (IO.userError warn)
  | .ok elffile => return elffile

open RawELFFile (getSymbolContents) in
/- Get the `st_value` of the symbol `symbolname` and its contents
(as a `ByteArray`). -/
def getSymbolContentsTop (symbolname : String) (elffile : RawELFFile) : IO (Nat × ByteArray) := do
  match (getSymbolContents elffile symbolname) with
  | .error warn => throw (IO.userError warn)
  | .ok (st_value, bytes) => return (st_value, bytes)

-------------------------------------------------------------------------------

def UInt8s.toUInt32s (xs : List UInt8) (isBigendian : Bool := false) : IO (List UInt32) :=
  match xs with
  | List.nil => pure List.nil
  | a :: b :: c :: d :: rest =>
    let val :=
    if isBigendian then
      (a.toNat <<< 24) + (b.toNat <<< 16) + (c.toNat <<< 8) + d.toNat
    else
      (d.toNat <<< 24) + (c.toNat <<< 16) + (b.toNat <<< 8) + a.toNat
    return (val.toUInt32 :: (← UInt8s.toUInt32s rest isBigendian))
  | _ =>  throw (IO.userError "Ill-formed input!")

def ByteArray.toUInt32s (xs : ByteArray) (isBigendian : Bool := false) : IO (List UInt32) :=
  UInt8s.toUInt32s xs.toList isBigendian

instance : ToString UInt32 where
  toString a := List.asString ('0' :: 'x' :: (Nat.toDigits 16 a.toNat))

/- `BitVec.enumFrom` is like `List.enumFrom`, but it lets you specify a
`BitVec n` index instead of a `Nat`. -/
def BitVec.enumFrom (i : BitVec n) (xs : List α) : List (BitVec n × α) :=
  match i, xs with
  | _, [] => List.nil
  | m, x :: xs   => (m, x) :: BitVec.enumFrom (m + 1) xs

/- Get the map for symbol `symbolname` in the file `elffile`. -/
def getSymbolMap (symbolname : String) (elffile : RawELFFile) : IO Program := do
  let (st_value, bytes) ← getSymbolContentsTop symbolname elffile
  let insts ← bytes.toUInt32s elffile.isBigendian
  let insts_bv := List.map
                    (fun (x : UInt32) =>
                      let x' := x.toNat
                      BitVec.ofNat 32 x')
                      insts
  return (BitVec.enumFrom (BitVec.ofNat 64 st_value) insts_bv)

/- Get the 32-bit words content for symbol `symbolname` in the file `elffile`. -/
def getSymbolWords (symbolname : String) (elffile : RawELFFile) : IO (List (BitVec 32)) := do
  let (_, bytes) ← getSymbolContentsTop symbolname elffile
  let insts ← bytes.toUInt32s elffile.isBigendian
  let insts_bv := List.map
                    (fun (x : UInt32) =>
                      let x' := x.toNat
                      BitVec.ofNat 32 x')
                      insts
  return insts_bv
