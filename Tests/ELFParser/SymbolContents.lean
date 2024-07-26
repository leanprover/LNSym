import ELFSage
import Arm.State

/- Given a file path, get the raw ELF file. -/
def getELFFile (elfFile : System.FilePath) : IO RawELFFile := do
  let bytes ← IO.FS.readBinFile elfFile
  match mkRawELFFile? bytes with
  | .error warn => throw (IO.userError warn)
  | .ok elffile => return elffile

/- Get the name and symbol table entry of the `symidx`-th symbol, given the
symbol table's section header `shte` and section `sec`. -/
def getSymbolTableEntryInSection
  (elffile : RawELFFile)
  (shte : RawSectionHeaderTableEntry)
  (sec : InterpretedSection)
  (symidx : Nat)
  : Except String (String × RawSymbolTableEntry) :=
    let offset := symidx * SectionHeaderTableEntry.sh_entsize shte
    (mkRawSymbolTableEntry?
      sec.section_body elffile.is64Bit elffile.isBigendian offset)
    >>= fun ste =>
          (symbolNameByLinkAndOffset
            elffile (SectionHeaderTableEntry.sh_link shte)
            (SymbolTableEntry.st_name ste))
    >>= fun sym_name => .ok (sym_name, ste)

/- Return the symbol table entry corresponding to a symbol `symname`, if it
exists, between entries with index greater than or equal to `symidx` and less
than `maxidx`. -/
def findSymbolTableEntryInSection
  (symidx maxidx : Nat)
  (elffile : RawELFFile)
  (shte : RawSectionHeaderTableEntry)
  (sec : InterpretedSection)
  (symname : String)
  : Except String RawSymbolTableEntry := do
  if symidx >= maxidx then
    .error s!"Symbol {symname} not found!"
  else
    (getSymbolTableEntryInSection elffile shte sec symidx)
    >>= fun (str, ste) =>
        if str == symname then
          return ste
        else
          findSymbolTableEntryInSection (symidx + 1) maxidx elffile shte sec symname
  termination_by (maxidx - symidx)

/- Get the `st_value` of the symbol `symbolname` and its contents
(as a `ByteArray`). -/
def getSymbolContents (symbolname : String) (elffile : RawELFFile) :
  Except String (Nat × ByteArray) := do
  (elffile.getSymbolTable?)
  >>= fun (shte, sec) =>
        let entry_size := SectionHeaderTableEntry.sh_entsize shte
        let table_size := SectionHeaderTableEntry.sh_size shte
        let total_entries := table_size / entry_size
        (findSymbolTableEntryInSection 0 total_entries elffile shte sec symbolname)
  >>= fun ste => SymbolTableEntry.toBody? ste elffile
  >>= fun bytes =>
         Except.ok (SymbolTableEntry.st_value ste, bytes)

/- Get the `st_value` of the symbol `symbolname` and its contents
(as a `ByteArray`). -/
def getSymbolContentsTop (symbolname : String) (elffile : RawELFFile) : IO (Nat × ByteArray) := do
  match (getSymbolContents symbolname elffile) with
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
