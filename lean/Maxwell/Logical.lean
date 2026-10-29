import Maxwell.Logical.Circuit
import Maxwell.Logical.CircuitMatrix
import Maxwell.Logical.Compile
import Maxwell.Logical.CompilerAlphabet
import Maxwell.Logical.CompilerFanout
import Maxwell.Logical.CircuitRows
import Maxwell.Logical.CopiedExpression
import Maxwell.Logical.CopiedResidual
import Maxwell.Logical.CopyTree
import Maxwell.Logical.Decoder
import Maxwell.Logical.DyadicCompile
import Maxwell.Logical.Gates
import Maxwell.Logical.Horner
import Maxwell.Logical.InputRecovery
import Maxwell.Logical.Path
import Maxwell.Logical.Rounding
import Maxwell.Logical.RationalSparse
import Maxwell.Logical.RationalValidity
import Maxwell.Logical.Routing
import Maxwell.Logical.Routing.BinaryDepth
import Maxwell.Logical.Routing.Subdivision
import Maxwell.Logical.SourceCircuit
import Maxwell.Logical.SourceInverse
import Maxwell.Logical.SourceSquare
import Maxwell.Logical.Usage

/-! The finite logical construction modules.

The imported declarations are genuine universal circuit, dyadic-arithmetic,
path-inverse, and rounding theorems. The complete sparse-to-cubic compiler
and its final resource theorem are under development; this import file
does not assume or assert their existence.
-/
