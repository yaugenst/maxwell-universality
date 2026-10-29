import Maxwell.Certificate.DyadicKernelGram
import Maxwell.Certificate.DyadicKernelSigned

namespace Maxwell.Certificate.DyadicKernel

def compressionRows {m n : Nat} (field action : Rectangular m n) : Rows n :=
  hermitianPartRows (crossRows 52 0 field action)

def signedCompressionRows {m n : Nat} (negative : Bool) (field action : Rectangular m n) : Rows n :=
  Rows.ofEnclosure fun i j => signedEntry negative ((compressionRows field action).enclosure i j) i j

def compressionEval {m n : Nat} (negative : Bool) (field action : Rectangular m n) : Bool :=
  schurEvalRows 52 (signedCompressionRows negative field action)

end Maxwell.Certificate.DyadicKernel
