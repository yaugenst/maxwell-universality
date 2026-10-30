import Maxwell.Continuum.CalibrationGlobalLinear

/-! Explicit real/imaginary coordinate blocks for one finite Fourier cube.
Sampling and zero extension are inverse on supported rational fields. -/

namespace Maxwell.Continuum.Calibration.GlobalPower
open FreeFiber
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

def realIndex (R : ℕ) : (Fin 2×Fin (aliasArraySize R))≃Fin (2*aliasArraySize R) :=
  finProdFinEquiv

def entry (R : ℕ) (f : RationalAliasField) (i : Fin (aliasArraySize R)) : RationalComplex :=
  f (arrayAlias R ((aliasArrayEquiv R).symm i).1) ((aliasArrayEquiv R).symm i).2

def sample (R : ℕ) (f : RationalAliasField) (i : Fin (2*aliasArraySize R)) : ℚ :=
  let p := (realIndex R).symm i
  if p.1=0 then (entry R f p.2).1 else (entry R f p.2).2

def unpack (R : ℕ) (x : Fin (2*aliasArraySize R)→ℚ) :
    Vector RationalComplex (aliasArraySize R) :=
  Vector.ofFn (fun i => (x (realIndex R (0,i)),x (realIndex R (1,i))))

def embed (R : ℕ) (x : Fin (2*aliasArraySize R)→ℚ) : RationalAliasField :=
  extendAliasArray R (unpack R x)

theorem sample_real (R : ℕ) (f : RationalAliasField) (i : Fin (aliasArraySize R)) :
    sample R f (realIndex R (0,i))=(entry R f i).1 := by
  simp [sample]

theorem sample_imag (R : ℕ) (f : RationalAliasField) (i : Fin (aliasArraySize R)) :
    sample R f (realIndex R (1,i))=(entry R f i).2 := by
  simp [sample]

theorem entry_embed (R : ℕ) (x : Fin (2*aliasArraySize R)→ℚ) (i : Fin (aliasArraySize R)) :
    entry R (embed R x) i=(x (realIndex R (0,i)),x (realIndex R (1,i))) := by
  unfold entry embed extendAliasArray
  rw [dite_eq_left (arrayAlias_mem R ((aliasArrayEquiv R).symm i).1)]
  simp only [arrayIndex_alias,Prod.mk.eta,Equiv.apply_symm_apply,unpack,vector_get_ofFn]

theorem sample_embed (R : ℕ) (x : Fin (2*aliasArraySize R)→ℚ) : sample R (embed R x)=x := by
  funext i
  obtain ⟨⟨c,j⟩,rfl⟩ := (realIndex R).surjective i
  fin_cases c
  · change sample R (embed R x) (realIndex R (0,j))=x (realIndex R (0,j))
    rw [sample_real,entry_embed]
  · change sample R (embed R x) (realIndex R (1,j))=x (realIndex R (1,j))
    rw [sample_imag,entry_embed]

theorem unpack_sample (R : ℕ) (f : RationalAliasField) :
    unpack R (sample R f)=sampleAliasArray R f := by
  apply Vector.ext
  intro i hi
  change (unpack R (sample R f)).get ⟨i,hi⟩=(sampleAliasArray R f).get ⟨i,hi⟩
  rw [unpack,sampleAliasArray,vector_get_ofFn,vector_get_ofFn,sample_real,sample_imag]
  rfl

theorem embed_sample {R : ℕ} {f : RationalAliasField} (hf : RationalSupported f R) :
    embed R (sample R f)=f := by
  rw [embed,unpack_sample]
  exact extend_sample_supported hf

theorem embed_supported (R : ℕ) (x : Fin (2*aliasArraySize R)→ℚ) :
    RationalSupported (embed R x) R :=
  FourierData.supported ⟨R,unpack R x⟩

def sampleLinear (R : ℕ) : RationalAliasField →ₗ[ℚ] (Fin (2*aliasArraySize R)→ℚ) where
  toFun := sample R
  map_add' f g := by
    funext i
    simp only [sample,entry,Pi.add_apply]
    split_ifs <;> rfl
  map_smul' c f := by
    funext i
    simp only [sample,entry,Pi.smul_apply]
    split_ifs <;> rfl

def embedLinear (R : ℕ) : (Fin (2*aliasArraySize R)→ℚ) →ₗ[ℚ] RationalAliasField where
  toFun := embed R
  map_add' x y := by
    funext ν j
    simp only [embed,extendAliasArray,Pi.add_apply]
    split_ifs
    · simp only [unpack,vector_get_ofFn,Pi.add_apply]
      rfl
    · exact (zero_add _).symm
  map_smul' c x := by
    funext ν j
    simp only [embed,extendAliasArray,Pi.smul_apply]
    split_ifs
    · simp only [unpack,vector_get_ofFn,Pi.smul_apply]
      rfl
    · exact (smul_zero c).symm

#print axioms sample_embed
#print axioms embed_sample

end Maxwell.Continuum.Calibration.GlobalPower
