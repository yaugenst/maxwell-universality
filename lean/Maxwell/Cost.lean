import Maxwell.Cost.Model
import Maxwell.Cost.Machine
import Maxwell.Cost.BitMachine
import Maxwell.Cost.BitRAM
import Maxwell.Cost.Compiler
import Maxwell.Cost.Saddle
import Maxwell.Cost.Precision
import Maxwell.Cost.Ambient
import Maxwell.Cost.Runner
import Maxwell.Cost.Transfer
import Maxwell.Cost.Arithmetic.Words
import Maxwell.Cost.Subtraction
import Maxwell.Cost.Multiplication.Frame
import Maxwell.Cost.SignedDifference.Frame
import Maxwell.Cost.Copy
import Maxwell.Cost.NormalizeWord
import Maxwell.Cost.EmitRat
import Maxwell.Cost.CountedLoop

/-!
# Operational resource accounting

* `BitRAM` is finite Boolean code with explicit binary addresses. Bit memory
  accesses consume the address length plus one microstep. `Machine` is the
  separate rational-constant finite-code Real RAM.
* Capped execution returns only a genuinely terminated state and obeys its
  time cap on every input and random tape. Output bits and random draws are
  charged. Fixed preprocessing is charged through an actual terminating run.
* Fixed Boolean programs implement arbitrary-width addition, subtraction,
  multiplication, signed magnitude difference, canonicalization and rational
  serialization. Their execution proofs charge every bit operation, tape
  traverse and linked return, with explicit output and preservation theorems.
* Additional arithmetic kernel specifications include sparse matrix-vector accumulation,
  full ambient cuboid emission, and comparison-based dyadic bisection.
  Their results, operation counts, errors and numerator lengths are proved.
* The computed routing port side gives an explicit `U^(3/2)` ambient-loop
  bound. The cap-to-exponent theorem uses actual finite-code machine runs,
  retains the construction exponent and absorbs fixed polylogarithms.

These modules do not identify the free-language kernel specifications with
compiled finite machine code for the entire physical reduction. Such a
compiler must supply actual code and its correctness/resource proof; neither
`Program.halt` nor a declared cost field establishes that identification.
-/
