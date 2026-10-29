import Maxwell.Continuum.EffectiveMassPacketIntegral

/-! Measurability and the uniform bound of the actual physical packet
wave, including the full infinite alias series. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber CellBandFourier Bloch BandWavePacket

theorem sectionValue_stronglyMeasurable : StronglyMeasurable sectionValue := by
  apply stronglyMeasurable_of_restrict_of_restrict_compl region_isOpen.measurableSet
  · have he : region.domRestrict sectionValue =
        region.domRestrict (fun q => FiberNormalization.normalizedFiberVector (parameter q)) := by
      funext q
      exact sectionValue_eq q.property
    rw [he]
    exact section_continuousOn.domRestrict.stronglyMeasurable
  · have he : regionᶜ.domRestrict sectionValue = fun _ => (0 : FiberSpace) := by
      funext q
      exact sectionValue_zero q.property
    rw [he]
    exact stronglyMeasurable_const

def packetWave (q : QuasiCell) (x : Space) : Polarization :=
  blochField (physicalMomentum q.val) (sectionValue q) x

theorem packetWave_norm (q : QuasiCell) (x : Space) : ‖packetWave q x‖ ≤ 32 := by
  rw [packetWave, blochField, norm_smul, spatialPhase_physical, angularPhase_norm, one_mul]
  exact (antiperiodicField_norm_le _ (sectionValue_fourier_l1 q).1 x).trans
    (sectionValue_fourier_l1 q).2

theorem packetWave_joint_measurable :
    StronglyMeasurable (fun xq : Space × QuasiCell => packetWave xq.2 xq.1) := by
  apply StronglyMeasurable.hasSum (L := SummationFilter.unconditional FreeFiber.Alias)
    (f := fun (ν : FreeFiber.Alias) (xq : Space × QuasiCell) =>
      aliasWave xq.2.val (sectionValue xq.2) xq.1 ν)
  · intro ν
    have hphase : Continuous (fun xq : Space × QuasiCell =>
        angularPhase (aliasFrequency xq.2.val ν) xq.1) := by
      unfold angularPhase aliasFrequency
      fun_prop
    have hcoeff : StronglyMeasurable (fun xq : Space × QuasiCell => sectionValue xq.2 ν) :=
      (lp.evalCLM ℂ (fun _ : FreeFiber.Alias => Polarization) 2 ν).continuous.comp_stronglyMeasurable
      (sectionValue_stronglyMeasurable.comp_measurable measurable_snd)
    exact hphase.stronglyMeasurable.smul hcoeff
  · intro xq
    exact aliasWave_hasSum xq.2.val (sectionValue xq.2) (sectionValue_fourier_l1 xq.2).1 xq.1

theorem packetWave_integrable (f : Amplitude) (x : Space) :
    Integrable (fun q => f.val q • packetWave q x) quasiMeasure := by
  apply (((Lp.memLp f.val).integrable (by norm_num)).norm.mul_const (32 : ℝ)).mono'
    ((Lp.stronglyMeasurable f.val).smul
      (packetWave_joint_measurable.comp_measurable measurable_prodMk_left)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun q => by
    change ‖f.val q • packetWave q x‖ ≤ ‖f.val q‖ * 32
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (packetWave_norm q x) (norm_nonneg _)

def fieldValue (u : FieldL2) (x : Space) : Polarization := WithLp.toLp 2 (fun j => u j x)

theorem field_inner_integrable (u v : FieldL2) :
    Integrable (fun x => inner ℂ (fieldValue u x) (fieldValue v x)) := by
  simp only [PiLp.inner_apply, fieldValue]
  exact integrable_finsetSum Finset.univ (fun j _ => L2.integrable_inner (u j) (v j))

theorem field_inner_eq_integral (u v : FieldL2) :
    inner ℂ u v = ∫ x, inner ℂ (fieldValue u x) (fieldValue v x) := by
  simp only [PiLp.inner_apply, fieldValue, L2.inner_def]
  exact (integral_finsetSum Finset.univ (fun j _ => L2.integrable_inner (u j) (v j))).symm

theorem fieldValue_Wh_ae (h : ℝ) (u : FieldL2) :
    fieldValue (Wh h u) =ᵐ[volume] fun x => (Well.w (h • x) : ℂ) • fieldValue u x := by
  filter_upwards [ae_all_iff.mpr (fun j => Wh_ae h u j)] with x hx
  apply PiLp.ext
  intro j
  exact hx j

theorem physicalEmbedding_vector_integral (f : Amplitude) :
    fieldValue (physicalEmbedding f) =ᵐ[volume]
      fun x => ∫ q : QuasiCell, f.val q • packetWave q x ∂quasiMeasure := by
  filter_upwards [ae_all_iff.mpr (physicalEmbedding_integral f)] with x hx
  apply PiLp.ext
  intro j
  have hp := (PiLp.proj 2 (fun _ : Fin 3 => ℂ) j : Polarization →L[ℂ] ℂ).integral_comp_comm
    (packetWave_integrable f x)
  change (∫ q, f.val q * packetWave q x j ∂quasiMeasure) =
    (∫ q, f.val q • packetWave q x ∂quasiMeasure) j at hp
  exact (hx j).trans hp

#print axioms packetWave_joint_measurable
#print axioms physicalEmbedding_vector_integral

end Maxwell.Continuum.EffectiveMass
