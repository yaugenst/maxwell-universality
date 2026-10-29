import Maxwell.Spectral.GlobalCubic.Action
import Maxwell.Certificate.FourierBinding

namespace Maxwell.Spectral.GlobalCubic
open PeriodicYee
open PrimitiveYee (Cell Electric RawCell Translation rawUnit latticeVector representative character)
open Maxwell.Certificate.FourierBinding (boundaryMomentum)
open scoped Matrix
set_option maxHeartbeats 1600000
noncomputable section

def momentum (g : Generator) (c : Momentum) : Momentum := match g with
  | .swap01 => ![c 1,c 0,c 2]
  | .swap12 => ![c 0,c 2,c 1]
  | .reflect0 => ![-c 0,c 1,c 2]

def translation (g : Generator) (n : Translation) : Translation := match g with
  | .swap01 => ![-n 0-n 2,2*n 0+n 1+n 2,n 2]
  | .swap12 => ![n 0,n 2,n 1]
  | .reflect0 => ![-n 0-n 1-n 2,n 1,n 2]

theorem momentum_involutive (g : Generator) (c : Momentum) : momentum g (momentum g c) = c := by
  cases g <;> funext i <;> fin_cases i <;> simp [momentum]

theorem node_translate (g : Generator) (a : ℤ) (r : RawCell) (n : Translation) :
    node g a (r+latticeVector n) = node g a r+latticeVector (translation g n) := by
  cases g <;> funext i <;> fin_cases i <;> simp [node, linear, latticeVector, translation] <;> ring

theorem character_translation (g : Generator) (c : Momentum) (n : Translation) :
    character (boundaryMomentum c) (translation g n) = character (boundaryMomentum (momentum g c)) n := by
  have hs : (∑ j, boundaryMomentum c j * ((translation g n j : ℤ) : ℝ)) =
      ∑ j, boundaryMomentum (momentum g c) j * (n j : ℝ) := by
    cases g <;> simp [boundaryMomentum, translation, momentum, Fin.sum_univ_three] <;> ring
  simpa only [character, Complex.ofReal_sum, Complex.ofReal_mul] using
    congrArg (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) hs

def Quasiperiodic (k : Momentum) (v : RawField) : Prop :=
  ∀ j r n, v j (r+latticeVector n) = character k n*v j r

theorem extend_quasiperiodic (k : Momentum) (v : Electric → ℂ) : Quasiperiodic k (extendField k v) :=
  fun _ r n => PrimitiveYee.extend_translate k _ r n

def restrict (v : RawField) : Electric → ℂ := fun e => v e.1 (representative e.2)

theorem restrict_extend (k : Momentum) (v : Electric → ℂ) : restrict (extendField k v) = v := by
  funext e
  simpa only [restrict, extendField, Prod.eta] using
    PrimitiveYee.extend_representative k (fun p => v (e.1,p)) e.2

theorem extend_restrict (k : Momentum) (v : RawField) (hv : Quasiperiodic k v) :
    extendField k (restrict v) = v := by
  funext j r
  have h := hv j (representative (PrimitiveYee.reduceCell r)) (PrimitiveYee.reduceTranslation r)
  rw [show representative (PrimitiveYee.reduceCell r)+latticeVector (PrimitiveYee.reduceTranslation r)=r
    from PrimitiveYee.reconstruct_reduce r] at h
  exact h.symm

theorem edgeAction_quasiperiodic (g : Generator) (a : ℤ) (c : Momentum) (v : RawField)
    (hv : Quasiperiodic (boundaryMomentum c) v) :
    Quasiperiodic (boundaryMomentum (momentum g c)) (edgeAction g a v) := by
  intro j r n
  unfold Quasiperiodic at hv
  have hshift (s t u : RawCell) : s+t-u=(s-u)+t := by abel
  cases g <;> fin_cases j <;>
    simp [edgeAction, node_translate, hshift, hv, character_translation]

theorem node_inverse (g : Generator) (a : ℤ) (r : RawCell) : node g a (node g (-a) r) = r := by
  cases g <;> funext i <;> fin_cases i <;> simp [node, linear]

theorem edgeAction_inverse (g : Generator) (a : ℤ) (v : RawField) :
    edgeAction g a (edgeAction g (-a) v) = v := by
  have hn : ∀ r, node g (-a) (node g a r) = r := fun r => by simpa using node_inverse g (-a) r
  funext j r
  cases g <;> fin_cases j <;> simp [edgeAction, node_sub_unit, unitImage, hn]

def transform (g : Generator) (a : ℤ) (c : Momentum) (v : Electric → ℂ) : Electric → ℂ :=
  restrict (edgeAction g a (extendField (boundaryMomentum c) v))

theorem extend_transform (g : Generator) (a : ℤ) (c : Momentum) (v : Electric → ℂ) :
    extendField (boundaryMomentum (momentum g c)) (transform g a c v) =
      edgeAction g a (extendField (boundaryMomentum c) v) :=
  extend_restrict _ _ (edgeAction_quasiperiodic g a c _ (extend_quasiperiodic _ v))

theorem transform_inverse (g : Generator) (a : ℤ) (c : Momentum) (v : Electric → ℂ) :
    transform g (-a) (momentum g c) (transform g a c v) = v := by
  unfold transform
  rw [show extendField (boundaryMomentum (momentum g c))
      (restrict (edgeAction g a (extendField (boundaryMomentum c) v))) =
      edgeAction g a (extendField (boundaryMomentum c) v) from extend_transform g a c v]
  have hi := edgeAction_inverse g (-a) (extendField (boundaryMomentum c) v)
  simp only [neg_neg] at hi
  rw [hi, restrict_extend]

end
end Maxwell.Spectral.GlobalCubic
