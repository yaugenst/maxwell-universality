import Maxwell.Continuum.CalibrationSupercellSupport
import Maxwell.Continuum.CalibrationCachedGrid

/-! All finite Bloch blocks are materialized once before global output
sampling. Both index conversions are executable equivalences. -/

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber

variable (M : ℕ) [NeZero M]

def gridTriple : Grid M ≃ (ZMod M × ZMod M × ZMod M) where
  toFun j := (j 0,j 1,j 2)
  invFun p := ![p.1,p.2.1,p.2.2]
  left_inv j := by funext i; fin_cases i <;> rfl
  right_inv p := by obtain ⟨a,b,c⟩ := p; rfl

def gridArrayEquiv : Grid M ≃ Fin (M*(M*M)) :=
  (gridTriple M).trans
    ((Equiv.prodCongr (ZMod.finEquiv M).toEquiv.symm
      (Equiv.prodCongr (ZMod.finEquiv M).toEquiv.symm (ZMod.finEquiv M).toEquiv.symm)).trans
        ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv))

def cachedApply {V : Type*} [AddCommGroup V] [Module ℚ V]
    (z σ : ℚ) (R K P : ℕ) (f : Alias → Fin 3 → V) :
    Vector V (aliasArraySize (outputRadius M R K)) :=
  let a := Vector.ofFn (fun i : Fin (M*(M*M)) =>
    let j := (gridArrayEquiv M).symm i
    cachedGridVector z σ (gridCoordinates M j) (fiberRadius M R) K P
      (fun ν k => f (join M (j,ν)) k))
  sampleAliasArray (outputRadius M R K) (fun n k =>
    let p := (indexEquiv M).symm n
    extendAliasArray (fiberRadius M R+K+2) (a.get (gridArrayEquiv M p.1)) p.2 k)

theorem cachedApply_eq {V : Type*} [AddCommGroup V] [Module ℚ V]
    (z σ : ℚ) (R K P : ℕ) {f : Alias → Fin 3 → V} (hf : RationalSupported f R) :
    extendAliasArray (outputRadius M R K) (cachedApply M z σ R K P f) = rationalApply M z σ K P f := by
  have hid : (fun n k =>
      let p := (indexEquiv M).symm n
      extendAliasArray (fiberRadius M R+K+2)
        ((Vector.ofFn (fun i : Fin (M*(M*M)) =>
          let j := (gridArrayEquiv M).symm i
          cachedGridVector z σ (gridCoordinates M j) (fiberRadius M R) K P
            (fun ν l => f (join M (j,ν)) l))).get (gridArrayEquiv M p.1)) p.2 k) =
      rationalApply M z σ K P f := by
    funext n k
    dsimp only
    rw [vector_get_ofFn,Equiv.symm_apply_apply]
    rw [cachedGridVector_eq z σ _ _ K P (rationalFiber_supported M hf _)]
    rfl
  unfold cachedApply
  dsimp only
  rw [hid]
  exact extend_sample_supported (rationalApply_supported M hf z σ K P)

#print axioms cachedApply_eq

end Maxwell.Continuum.Calibration.Supercell
