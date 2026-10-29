import Maxwell.Composition.SelectedInstance
import Maxwell.Main

/-! Every emitted scalar cell and source entry is dyadic on every draw.
This includes the fixed periodic material and the finite uniform shift. -/
noncomputable section
namespace Maxwell.Realization.IsDyadic

theorem integer (z : ℤ) : IsDyadic (z:ℚ) := ⟨0,⟨z⟩,by simp [Dyadic.value]⟩
theorem natural (n : ℕ) : IsDyadic (n:ℚ) := by exact_mod_cast integer (n:ℤ)
theorem inverse_power (b : ℕ) : IsDyadic ((2:ℚ)^b)⁻¹ :=
  ⟨b,⟨1⟩,by simp [Dyadic.value]⟩

theorem add {a b : ℚ} (ha : IsDyadic a) (hb : IsDyadic b) : IsDyadic (a+b) := by
  obtain ⟨p,⟨z⟩,rfl⟩ := ha
  obtain ⟨q,⟨w⟩,rfl⟩ := hb
  refine ⟨p+q,⟨z*2^q+w*2^p⟩,?_⟩
  simp only [Dyadic.value,Int.cast_add,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,pow_add]
  field_simp

theorem mul {a b : ℚ} (ha : IsDyadic a) (hb : IsDyadic b) : IsDyadic (a*b) := by
  obtain ⟨p,⟨z⟩,rfl⟩ := ha
  obtain ⟨q,⟨w⟩,rfl⟩ := hb
  refine ⟨p+q,⟨z*w⟩,?_⟩
  simp [Dyadic.value,pow_add,mul_div_mul_comm]

theorem sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, IsDyadic (f i)) :
    IsDyadic (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using integer 0
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact add (h a (by simp)) (ih (fun i hi => h i (by simp [hi])))

theorem selectedUnit (q : ℚ) (hq : 0 < q) : IsDyadic (precisionUnit q hq) :=
  ⟨_,selectedDyadic q hq,selectedDyadic_value q hq⟩

end Maxwell.Realization.IsDyadic

namespace Maxwell.Composition.SelectedDyadic
open Maxwell.Realization Maxwell.Defect Maxwell.Spectral Maxwell.Spectral.Lattice
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000

theorem candidate (i : ℕ) : IsDyadic (dyadicCandidate i) := by
  change IsDyadic ((Nat.unpair i).1 / (2:ℚ)^(Nat.unpair i).2)
  rw [div_eq_mul_inv]
  exact IsDyadic.mul (IsDyadic.natural _) (IsDyadic.inverse_power _)

theorem fixedMaterial (r : Cell20) : IsDyadic (FiniteStencil.frozenMaterialQ r) := by
  unfold FiniteStencil.frozenMaterialQ Maxwell.Certificate.Material.cellValue
  apply IsDyadic.add
  · unfold Maxwell.Certificate.Material.baseValue
    split <;> exact IsDyadic.natural _
  · have h := IsDyadic.mul
      (IsDyadic.natural (Maxwell.Certificate.Material.numerator
        ⟨(r 0).val,ZMod.val_lt _⟩ ⟨(r 1).val,ZMod.val_lt _⟩ ⟨(r 2).val,ZMod.val_lt _⟩))
      (IsDyadic.inverse_power 21)
    norm_num only [pow_succ,pow_zero] at h
    convert h using 1
    norm_num [div_eq_mul_inv]

theorem background (R : SelectedPlatform) (r : Cell20) : IsDyadic (R.physical.background.material r) := by
  rw [R.material_eq]
  exact IsDyadic.add (fixedMaterial r) (IsDyadic.mul (IsDyadic.natural 64) (candidate R.certificate.index))

variable (I : SelectedInstance.Input) (R : SelectedPlatform)

theorem increment (i : SourceDecoration.Vertex I.source I.precision) : IsDyadic (I.increment R i) := by
  unfold SelectedInstance.Input.increment PhysicalCalibrated.increment
  exact ⟨_,_,rfl⟩

theorem detuning : IsDyadic (PhysicalGram.width R.physical (I.zeta R) (I.zeta_pos R)) :=
  IsDyadic.selectedUnit _ _

theorem midpoint (bits : ℕ) (j : Fin (2^bits)) :
    IsDyadic (PhysicalMaterial.sigma R.physical (I.zeta R) (I.zeta_pos R) (2^bits) j) := by
  unfold PhysicalMaterial.sigma Probability.rationalMidpoint
  norm_num only [Nat.cast_pow,Nat.cast_ofNat]
  rw [div_eq_mul_inv]
  apply IsDyadic.mul
  · apply IsDyadic.mul
    · apply IsDyadic.add (IsDyadic.natural _)
      simpa using IsDyadic.inverse_power 1
    · exact detuning I R
  · exact IsDyadic.inverse_power bits

theorem material (bits : ℕ) (j : Fin (2^bits)) (c : (I.target R (2^bits) j).box.Cell) :
    IsDyadic ((I.target R (2^bits) j).material.value c) := by
  change IsDyadic (PhysicalMaterial.backgroundValue R.physical I.source I.precision (I.distance R)
    (I.zeta R) (I.zeta_pos R) (I.zeta_one R) (2^bits) j c +
    64*∑ i, I.increment R i * Target.defectIndicator
      (DecoratedDefectLayout.cellBlocks I.source I.precision R.physical.basis R.physical.defect
        (I.distance R) (R.physical.chosenBuffer I.source I.precision (I.distance R)
          (I.zeta R) (I.zeta_pos R) (I.zeta_one R)) i) c)
  apply IsDyadic.add
  · exact IsDyadic.add (background R _) (IsDyadic.mul (IsDyadic.natural 64) (midpoint I R bits j))
  · apply IsDyadic.mul (IsDyadic.natural 64)
    apply IsDyadic.sum
    intro i _
    apply IsDyadic.mul (increment I R i)
    unfold Target.defectIndicator
    split <;> exact IsDyadic.natural _

theorem source (J : ℕ) (j : Fin J) (e : (I.target R J j).box.Edge) :
    IsDyadic ((I.target R J j).source e) := by
  exact ⟨_,_,rfl⟩

theorem tolerance (J : ℕ) (j : Fin J) : IsDyadic (I.target R J j).tolerance :=
  IsDyadic.selectedUnit _ _

end Maxwell.Composition.SelectedDyadic
