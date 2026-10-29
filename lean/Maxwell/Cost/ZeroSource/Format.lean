import Maxwell.BaseCases
import Maxwell.Codec

namespace Maxwell.Cost.ZeroSource

/-- The one-edge physical instance has a fixed header. Only the original
source dimension and its repeated empty decoder rows vary with input. -/
def header : List Bool :=
  Codec.nat BaseCases.box.nx ++ Codec.nat BaseCases.box.ny ++ Codec.nat BaseCases.box.nz ++
    Codec.list (fun c => Codec.rat (BaseCases.material.value c)) (Codec.cells BaseCases.box) ++
    Codec.list (fun _ : BaseCases.box.Edge => Codec.rat 0) (Codec.edges BaseCases.box) ++
    Codec.rat 1 ++ Codec.nat 0 ++ Codec.nat 0 ++ Codec.nat 0

def row : List Bool := Codec.rat 0 ++ Codec.nat 0

def targetBits (n : ℕ) : List Bool :=
  Codec.nat n ++ header ++ Codec.nat n ++ (List.replicate n row).flatten

theorem targetBits_eq (S : Source.SparseSystem) :
    Codec.target (BaseCases.zeroInstance S) = targetBits S.n := by
  simp [Codec.target, Codec.decoder, Codec.list, BaseCases.zeroInstance, BaseCases.zeroDecoder,
    header, row, targetBits, List.append_assoc]
  rw [List.flatMap_def, List.map_const', List.length_finRange]

end Maxwell.Cost.ZeroSource
