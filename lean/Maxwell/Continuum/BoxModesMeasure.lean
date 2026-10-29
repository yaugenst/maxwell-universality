import Maxwell.Continuum.BoxModesL2

/-!
# Identification of the mode measure with physical box volume

The coordinate cube carries unnormalized product Lebesgue measure. Its
canonical embedding into Euclidean three-space preserves exactly Lebesgue
measure restricted to the open physical box; boundary faces have measure zero.
-/

noncomputable section
namespace Maxwell.Continuum.BoxModes

open MeasureTheory
open scoped InnerProductSpace ENNReal

theorem cubePoint_injective (N : Fin 3 → ℝ) : Function.Injective (cubePoint N) := by
  intro x y h
  funext j
  apply Subtype.ext
  exact congrArg (fun z : Point => z j) h

theorem cubePoint_measurableEmbedding (N : Fin 3 → ℝ) :
    MeasurableEmbedding (cubePoint N) :=
  ((continuous_cubePoint N).isClosedEmbedding (cubePoint_injective N)).measurableEmbedding

/-- Exact physical, unnormalized volume preservation. -/
theorem cubePoint_measurePreserving (N : Fin 3 → ℝ) :
    MeasurePreserving (cubePoint N) (cubeMeasure N) (volume.restrict (openBox N)) := by
  have hi (j : Fin 3) : MeasurePreserving
      (Subtype.val : Set.Icc (0 : ℝ) (N j) → ℝ)
      (intervalMeasure (N j)) (volume.restrict (Set.Ioo 0 (N j))) := by
    rw [restrict_Ioo_eq_restrict_Icc]
    exact measurePreserving_subtype_coe measurableSet_Icc
  have hp := measurePreserving_pi (fun j => intervalMeasure (N j))
    (fun j => volume.restrict (Set.Ioo 0 (N j))) hi
  have ht := (PiLp.volume_preserving_toLp (Fin 3)).restrict_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding (openBox N)
  have heq : (@WithLp.toLp 2 (Fin 3 → ℝ)) ⁻¹' openBox N =
      Set.univ.pi (fun j => Set.Ioo 0 (N j)) := by
    ext x
    rfl
  rw [heq] at ht
  change MeasurePreserving (@WithLp.toLp 2 (Fin 3 → ℝ))
    ((Measure.pi fun _ : Fin 3 => (volume : Measure ℝ)).restrict
      (Set.univ.pi (fun j => Set.Ioo 0 (N j))))
    (volume.restrict (openBox N)) at ht
  rw [Measure.restrict_pi_pi] at ht
  exact ht.comp hp

/-- Change of variables from the compact coordinate box to the actual open
Euclidean box. No boundary term or volume normalization occurs. -/
theorem integral_cubePoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : Fin 3 → ℝ) (f : Point → E) :
    (∫ x, f (cubePoint N x) ∂cubeMeasure N) = ∫ x in openBox N, f x :=
  (cubePoint_measurePreserving N).integral_comp (cubePoint_measurableEmbedding N) f

theorem memLp_cubePoint_iff {E : Type*} [NormedAddCommGroup E]
    (N : Fin 3 → ℝ) (f : Point → E) (p : ℝ≥0∞) :
    MemLp (f ∘ cubePoint N) p (cubeMeasure N) ↔
      MemLp f p (volume.restrict (openBox N)) := by
  rw [← (cubePoint_measurePreserving N).map_eq]
  exact (cubePoint_measurableEmbedding N).memLp_map_measure_iff.symm

abbrev BoxL2 (N : Fin 3 → ℝ) := Lp ℝ 2 (volume.restrict (openBox N))

/-- Pullback is an isometry between physical L² and coordinate L². -/
def boxL2Pullback (N : Fin 3 → ℝ) : BoxL2 N →ₗᵢ[ℝ] CubeL2 N :=
  Lp.compMeasurePreservingₗᵢ ℝ (cubePoint N) (cubePoint_measurePreserving N)

theorem memLp_scalarBoxMode (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c : Fin 3) :
    MemLp (scalarBoxMode N ν c) 2 (volume.restrict (openBox N)) := by
  apply (memLp_cubePoint_iff N _ _).mp
  have h := ContinuousMap.memLp (p := 2) (cubeMeasure N) ℝ (cubeMode N c ν)
  have he : (cubeMode N c ν : ClosedCube N → ℝ) =
      scalarBoxMode N ν c ∘ cubePoint N := funext (cubeMode_apply N c ν)
  rw [he] at h
  exact h

def boxModeL2 (N : Fin 3 → ℝ) (c : Fin 3) (ν : Fin 3 → ℤ) : BoxL2 N :=
  (memLp_scalarBoxMode N ν c).toLp (scalarBoxMode N ν c)

theorem boxModeL2_pullback (N : Fin 3 → ℝ) (c : Fin 3) (ν : Fin 3 → ℤ) :
    boxL2Pullback N (boxModeL2 N c ν) = cubeModeL2 N c ν := by
  apply Lp.ext
  have hp := Lp.coeFn_compMeasurePreserving (boxModeL2 N c ν)
    (cubePoint_measurePreserving N)
  have hs := (cubePoint_measurePreserving N).quasiMeasurePreserving.ae
    ((memLp_scalarBoxMode N ν c).coeFn_toLp)
  filter_upwards [hp, hs, ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ)
    (cubeMeasure N) (cubeMode N c ν)] with x hx hsx hcx
  exact hx.trans (hsx.trans (cubeMode_apply N c ν x).symm) |>.trans hcx.symm

#print axioms cubePoint_measurePreserving
#print axioms boxModeL2_pullback

end Maxwell.Continuum.BoxModes
