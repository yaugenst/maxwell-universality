import Maxwell.Continuum.CalibrationSeed
import Maxwell.Continuum.CalibrationFiniteData
import Maxwell.Continuum.CalibrationSupercellSupport

/-! The executable finite Fourier seed in the zero Bloch-grid block.
Its factor i is the literal physical-cell reality convention. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber

namespace Supercell

variable (M : ℕ) [NeZero M]

def rationalInjection (j : Grid M) (f : RationalAliasField) : RationalAliasField := fun n i =>
  let p := (indexEquiv M).symm n
  if p.1=j then f p.2 i else 0

theorem rationalInjection_join (j k : Grid M) (f : RationalAliasField) (ν : Alias) (i : Fin 3) :
    rationalInjection M j f (join M (k,ν)) i = if k=j then f ν i else 0 := by
  change (if ((indexEquiv M).symm ((indexEquiv M) (k,ν))).1=j then
    f ((indexEquiv M).symm ((indexEquiv M) (k,ν))).2 i else 0)=_
  rw [Equiv.symm_apply_apply]

theorem rationalInjection_supported {f : RationalAliasField} {R : ℕ}
    (hf : RationalSupported f R) (j : Grid M) :
    RationalSupported (rationalInjection M j f) (M*(R+2)) := by
  intro n hn i
  obtain ⟨⟨k,ν⟩,rfl⟩ := (indexEquiv M).surjective n
  change rationalInjection M j f (join M (k,ν)) i = 0
  rw [rationalInjection_join]
  split_ifs
  · apply hf ν
    obtain ⟨l,hl⟩ := hn
    refine ⟨l,?_⟩
    have hm : 0 ≤ (M : ℤ) := Int.natCast_nonneg _
    have hb := joinCoordinate_abs M (k l) (ν l)
    change ((M*(R+2) : ℕ) : ℤ) < |joinCoordinate M (k l,ν l)| at hl
    simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] at hl
    by_contra h
    have hle : |ν l| ≤ (R : ℤ) := le_of_not_gt h
    nlinarith
  · rfl

noncomputable def injection (j : Grid M) (u : FiberSpace) : FiberSpace :=
  (unitary M).symm (PiLp.single 2 j u)

theorem injection_join (j k : Grid M) (u : FiberSpace) (ν : Alias) :
    injection M j u (join M (k,ν)) = if k=j then u ν else 0 := by
  rw [injection,unitary_symm_apply]
  by_cases h : k=j
  · subst k
    simp
  · simp [h]

theorem rationalInjection_represents (j : Grid M) {f : RationalAliasField} {u : FiberSpace}
    (hf : Represents f u) : Represents (rationalInjection M j f) (injection M j u) := by
  intro n i
  obtain ⟨⟨k,ν⟩,rfl⟩ := (indexEquiv M).surjective n
  change rationalComplexValue (rationalInjection M j f (join M (k,ν)) i) =
    injection M j u (join M (k,ν)) i
  rw [rationalInjection_join,injection_join]
  split_ifs
  · exact hf ν i
  · exact map_zero rationalComplexLinear

theorem injection_norm (j : Grid M) (u : FiberSpace) : ‖injection M j u‖=‖u‖ := by
  rw [injection,LinearIsometryEquiv.norm_map,PiLp.norm_single]

theorem injection_sub (j : Grid M) (u v : FiberSpace) :
    injection M j u-injection M j v=injection M j (u-v) := by
  rw [injection,injection,← map_sub]
  congr 1
  ext k
  simp only [PiLp.sub_apply,PiLp.single_apply]
  split_ifs <;> simp

def rationalPhase (f : RationalAliasField) : RationalAliasField :=
  fun ν i => rationalComplexMul (0,1) (f ν i)

theorem rationalPhase_represents {f : RationalAliasField} {u : FiberSpace}
    (hf : Represents f u) : Represents (rationalPhase f) (Complex.I • u) := by
  intro ν i
  rw [rationalPhase,rationalComplexMul_value,hf]
  have he : rationalComplexValue (0,1)=Complex.I := by simp [rationalComplexValue_eq]
  rw [he]
  rfl

theorem rationalPhase_supported {f : RationalAliasField} {R : ℕ}
    (hf : RationalSupported f R) : RationalSupported (rationalPhase f) R := by
  intro ν hν i
  rw [rationalPhase,hf ν hν i,rationalComplexMul_zero]

def finiteSeed (N : ℕ) : FourierData :=
  FourierData.ofSupported (rationalPhase (rationalInjection M 0 (rationalSeed N))) (M*(1+2))

theorem finiteSeed_value (N : ℕ) :
    (finiteSeed M N).value=Complex.I • injection M 0 (seedVector N) :=
  FourierData.ofSupported_value
    (rationalPhase_supported (rationalInjection_supported M (rationalSeed_supported N) 0))
    (rationalPhase_represents (rationalInjection_represents M 0 (seed_represents N)))

theorem finiteSeed_error (N : ℕ) :
    ‖(finiteSeed M N).value-Complex.I • injection M 0 CornerBridge.topState.val‖ ≤ (1/2 : ℝ)^N := by
  rw [finiteSeed_value,← smul_sub,norm_smul,Complex.norm_I,one_mul,
    injection_sub,injection_norm]
  exact seedVector_error N

#print axioms finiteSeed_value
#print axioms finiteSeed_error

end Supercell
end Maxwell.Continuum.Calibration
