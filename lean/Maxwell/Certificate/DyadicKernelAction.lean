import Maxwell.Certificate.DyadicKernelVector
import Maxwell.Certificate.GlobalFFTComputed.Constants

/-! Deterministic projected magnetic action. All spatial arrays and FFT
stages are computed from the input rectangles. -/
namespace Maxwell.Certificate.DyadicKernel.Action
noncomputable section

abbrev Cell := Fin 20 × Fin 10 × Fin 10

structure VectorField where
  x : FFT.Field
  y : FFT.Field
  z : FFT.Field

def VectorField.component (a : VectorField) (j : Fin 3) : FFT.Field :=
  match j.val with | 0 => a.x | 1 => a.y | _ => a.z

def VectorField.get (a : VectorField) (r : Cell) : Triple :=
  ⟨FFT.get a.x r.1 r.2.1 r.2.2, FFT.get a.y r.1 r.2.1 r.2.2,
    FFT.get a.z r.1 r.2.1 r.2.2⟩

def VectorField.build (a : Cell → Triple) : VectorField :=
  ⟨FFT.build fun x y z => (a (x,y,z)).x,
   FFT.build fun x y z => (a (x,y,z)).y,
   FFT.build fun x y z => (a (x,y,z)).z⟩

def VectorField.map (f : FFT.Field → FFT.Field) (a : VectorField) : VectorField :=
  ⟨f a.x,f a.y,f a.z⟩

def zeroTriple : Triple := ⟨zero,zero,zero⟩

def allFin (n : Nat) (p : Fin n → Bool) : Bool := (List.finRange n).all p

theorem allFin_sound {n : Nat} {p : Fin n → Bool} (h : allFin n p = true) (i : Fin n) :
    p i = true := List.all_eq_true.mp h i (List.mem_finRange i)

def projectionValid (d : VectorField) : Bool :=
  allFin 20 fun x => allFin 10 fun y => allFin 10 fun z => decide
    (0 < (laplacianRound 52 (d.get (x,y,z))).re-
      ((laplacianRound 52 (d.get (x,y,z))).radius : Int))

def materialValid (m : VectorField) : Bool :=
  allFin 20 fun x => allFin 10 fun y => allFin 10 fun z => allFin 3 fun j => decide
    (0 < ((m.get (x,y,z)).get j).re-(((m.get (x,y,z)).get j).radius : Int))

theorem projectionValid_pos {d : VectorField} (h : projectionValid d = true) (r : Cell) :
    0 < (laplacianRound 52 (d.get r)).re-((laplacianRound 52 (d.get r)).radius : Int) := by
  exact of_decide_eq_true (allFin_sound (allFin_sound (allFin_sound h r.1) r.2.1) r.2.2)

theorem materialValid_pos {m : VectorField} (h : materialValid m = true) (r : Cell) (j : Fin 3) :
    0 < ((m.get r).get j).re-(((m.get r).get j).radius : Int) := by
  exact of_decide_eq_true
    (allFin_sound (allFin_sound (allFin_sound (allFin_sound h r.1) r.2.1) r.2.2) j)

def project (d raw : VectorField) : VectorField := VectorField.build fun r =>
  (projectRound 52 (d.get r) (raw.get r) (laplacianRound 52 (d.get r))).getD zeroTriple

def adjointCurl (d field : VectorField) : VectorField := VectorField.build fun r =>
  curlRound 52 true (d.get r) (field.get r)

def inverse (field : VectorField) : VectorField := field.map
  (FFT.inverse 52 GlobalFFTComputed.kernel20 GlobalFFTComputed.kernel10 GlobalFFTComputed.twiddle)

def divideMaterial (field material : VectorField) : VectorField := VectorField.build fun r =>
  (divideTriple 52 (field.get r) (material.get r)).getD zeroTriple

def forward (field : VectorField) : VectorField := field.map
  (FFT.forward 52 GlobalFFTComputed.kernel20 GlobalFFTComputed.kernel10 GlobalFFTComputed.twiddle)

def magnetic (d weighted field : VectorField) : VectorField := VectorField.build fun r =>
  magneticRound (d.get r) (weighted.get r) (field.get r)

structure Result where
  projected : VectorField
  curl : VectorField
  weighted : VectorField
  action : VectorField

def compute (d material raw : VectorField) : Result :=
  let projected := project d raw
  let curl := adjointCurl d projected
  let weighted := forward (divideMaterial (inverse curl) material)
  ⟨projected,curl,weighted,magnetic d weighted projected⟩

/-- Failure is exactly failure of a positive input denominator test. -/
def evaluate (d material raw : VectorField) : Option Result :=
  if projectionValid d && materialValid material then some (compute d material raw) else none

end
end Maxwell.Certificate.DyadicKernel.Action
