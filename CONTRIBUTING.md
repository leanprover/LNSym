# Contribution Guidelines

## Project status

Amazon Confidential

LNSym is an Amazon-internal project. Please do not make any external
contributions at this time.

### Test Your Contribution

1. Start from a clean slate; remove previous build artifacts using
   `make clean_all`.

2. Follow the LNSym build instructions in the README.md (including
   conformance testing on an Aarch64 machine) before submitting your
   pull request.

## FAQs

### How do I add a new Arm instruction?

1. **Decode:** Add support, if needed, for decoding the instruction's
   class to LNSym's Arm decoder (function `decode_raw_inst` in
   `Arm/Decode.lean`).  See Section C4.1 in Part A of the [Arm
   manual's
   PDF](https://developer.arm.com/documentation/ddi0487/latest) to
   learn about Arm's instruction classes.

   An `ArmInst` type describes a fully-decoded Arm instruction. It
   contains constructors that correspond to the currently supported
   instruction classes. For example, the `DPI` constructor represents
   the data processing (immediate) instructions, which have several
   sub-classes which are formalized in `Arm/Decode/DPI/DPI.lean`.

2. **Instruction Semantics:** Formalize the instruction's behavior in
   a file under an appropriate directory pertaining to the instruction
   class (under `Arm/Insts`). You may either need to extend a
   pre-existing function (perhaps it supported only a subset of the
   instructions in that class, and you can add your new instruction
   right there), or add a new directory/file/function altogether.

   For example, `Arm/Insts/DPI/Add_sub_imm.lean` contains the
   semantics of all instructions (e.g., `ADD`) under the `Add_sub_imm`
   sub-class of data processsing (immediate) instructions.

   Also add a function to generate random instructions of that class;
   this will be used to validate the instruction semantics via
   conformance testing. For an example, see the function
   `Add_sub_imm_cls.rand` defined in the same file as the instruction
   semantics. These functions should be eventually added to
   `Insts.rand` in `Arm/Insts.lean`, which is used to run
   co-simulations when `build/bin/lnsym` is executed.

   You do not need to know how these co-simulations are run, but an
   interested reader can see `Arm/Cosim.lean` and `Arm/Main.lean` for
   details.

3. **Execute:** Add support, if needed, to execute this instruction by
   extending the function `exec_inst` in `Arm/Exec.lean` .

4. **Build and Test:** Run `make` to make sure nothing breaks as a
   consequence of your addition. Also run `make cosim` on an Aarch64
   machine to run conformance tests for validating your new
   instruction.
