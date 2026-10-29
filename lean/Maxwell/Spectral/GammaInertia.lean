import Maxwell.Spectral.GammaSymbols
import Maxwell.Spectral.BoxHighCoercivity
import Maxwell.Certificate.FourierElectricInertia

/-! The full Gamma comparison, including zero momentum. High transverse
frequencies have dimension 3998; their orthogonal complement has dimension
2002 and is strictly negative. No projector at the zero symbol is inverted. -/

noncomputable section
namespace Maxwell.Spectral.GammaInertia
open Maxwell.Certificate.FourierBinding Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Momentum Direction)
open BoxHighCoercivity
set_option maxRecDepth 4000

abbrev highFrequencies : Finset Frequency := Finset.univ.erase 0
abbrev highSpace (c : Momentum) := supportedTransverseSubspace c highFrequencies

theorem highSpace_finrank_of_nonzero (c : Momentum)
    (hc : ∀ f : Frequency, f ≠ 0 → laplacianSymbol c f ≠ 0) : Module.finrank ℂ (highSpace c) = 3998 := by
  rw [← (supportedTransverseCoordinatesEquiv c highFrequencies).finrank_eq,
    (WithLp.linearEquiv 2 ℂ _).finrank_eq, Module.finrank_pi_fintype]
  have hf (f : {f // f ∈ highFrequencies}) :
      Module.finrank ℂ (transversePolarization c f) = 2 := by
    apply transversePolarization_finrank
    have hn : (f : Frequency) ≠ 0 := (Finset.mem_erase.mp f.property).1
    exact hc f hn
  simp only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [Fintype.card_coe]
  simp only [highFrequencies, Finset.card_erase_of_mem (Finset.mem_univ (0 : Frequency)), Finset.card_univ]
  norm_num [Frequency, Cell]

theorem highSpace_finrank (c : Momentum)
    (hc : ∀ j, |c j| ≤ 1/8) : Module.finrank ℂ (highSpace c) = 3998 :=
  highSpace_finrank_of_nonzero c fun f hf =>
    ne_of_gt (lt_trans (by norm_num) (GammaSymbols.gamma_high c hc f hf))

theorem highSpace_orthogonal_finrank (c : Momentum)
    (hc : ∀ j, |c j| ≤ 1/8) : Module.finrank ℂ (highSpace c)ᗮ = 2002 := by
  have h := (highSpace c).finrank_add_finrank_orthogonal
  rw [highSpace_finrank c hc] at h
  have hd : Module.finrank ℂ FourierSpace = 6000 := by
    simp [FourierSpace, Electric, Cell]
  rw [hd] at h
  omega

/-- Orthogonality to the high transverse space eliminates exactly those
components of the full transverse projection. -/
theorem high_transverse_eq_zero (c : Momentum) (x : FourierSpace)
    (hx : x ∈ (highSpace c)ᗮ) :
    frequencyRestriction highFrequencies (transversePart c x) = 0 := by
  let y := frequencyRestriction highFrequencies (transversePart c x)
  let z := frequencyRestriction highFrequenciesᶜ (transversePart c x)
  have hy : y ∈ highSpace c := frequencyRestriction_mem c _ _ (transversePart_mem c x)
  have hz : z ∈ supportedTransverseSubspace c highFrequenciesᶜ :=
    frequencyRestriction_mem c _ _ (transversePart_mem c x)
  have hyz : inner ℂ y z = 0 := supportedTransverse_orthogonal_compl c _ y z hy hz
  have hyl : inner ℂ y (longitudinalPart c x) = 0 :=
    ((transverseSubspace c).mem_orthogonal _).mp
      (longitudinalProjection_mem_orthogonal c x) y hy.1
  have hyx : inner ℂ y x = 0 := ((highSpace c).mem_orthogonal x).mp hx y hy
  have hdec : x = y + z + longitudinalPart c x := by
    dsimp [y, z]
    rw [frequencyRestriction_add_compl]
    simp only [transversePart, LinearMap.sub_apply, LinearMap.id_apply, sub_add_cancel]
  rw [hdec, inner_add_right, inner_add_right, hyz, hyl, add_zero, add_zero] at hyx
  exact inner_self_eq_zero.mp hyx

theorem high_transverse_component_zero (c : Momentum) (x : FourierSpace)
    (hx : x ∈ (highSpace c)ᗮ) (f : Frequency) (hf : f ≠ 0) :
    frequencyComponent f (transversePart c x) = 0 := by
  have h := high_transverse_eq_zero c x hx
  ext j
  have he := congrArg (fun z : FourierSpace => z (j, f)) h
  change (transversePart c x) (j, f) = 0
  simpa [frequencyRestriction, highFrequencies, hf] using he

/-- The curl energy on the negative trial space is bounded by the single
low Gamma symbol, even when that symbol is exactly zero. -/
theorem orthogonal_curl_bound (c : Momentum) (x : FourierSpace)
    (hx : x ∈ (highSpace c)ᗮ) :
    ‖(frequencyCurl c).conjTranspose.toEuclideanLin x‖^2 ≤ laplacianSymbol c 0 * ‖x‖^2 := by
  rw [curl_adjoint_norm_sq_parts]
  have hs : (∑ f, laplacianSymbol c f * ‖frequencyComponent f (transversePart c x)‖^2) =
      laplacianSymbol c 0 * ‖frequencyComponent 0 (transversePart c x)‖^2 := by
    apply Finset.sum_eq_single 0
    · intro f _ hf
      rw [high_transverse_component_zero c x hx f hf, norm_zero, zero_pow (by decide), mul_zero]
    · simp
  rw [hs]
  have hc0 : ‖frequencyComponent 0 (transversePart c x)‖^2 ≤ ‖transversePart c x‖^2 := by
    rw [norm_sq_frequencyComponents]
    exact Finset.single_le_sum
      (f := fun f : Frequency => ‖frequencyComponent f (transversePart c x)‖^2)
      (fun f _ => sq_nonneg _) (Finset.mem_univ 0)
  have ht : ‖transversePart c x‖^2 ≤ ‖x‖^2 := by
    rw [parts_norm_sq c x]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hl : 0 ≤ laplacianSymbol c 0 := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  exact mul_le_mul_of_nonneg_left (hc0.trans ht) hl

theorem shifted_energy (material : PeriodicYee.Cell20 → ℝ) (c : Momentum)
    (t : ℝ) (x : FourierSpace) :
    (inner ℂ x ((shiftedMagneticFourier material c t).toEuclideanLin x)).re =
      (inner ℂ ((frequencyCurl c).conjTranspose.toEuclideanLin x)
        ((fourierInverseMass material).toEuclideanLin
          ((frequencyCurl c).conjTranspose.toEuclideanLin x))).re - t*‖x‖^2 := by
  simp only [shiftedMagneticFourier, map_sub, map_smul, Matrix.toLpLin_mul_same,
    Matrix.toLpLin_one, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.id_apply, inner_sub_right, Complex.sub_re,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [← LinearMap.adjoint_inner_left]
  simp only [inner_smul_right, inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem orthogonal_negative_of_low (material : PeriodicYee.Cell20 → ℝ)
    (hm : ∀ e, 1 ≤ edgeAverage material e) (c : Momentum)
    (t : ℝ) (ht : laplacianSymbol c 0 < t)
    (x : (highSpace c)ᗮ) (hx : x ≠ 0) :
    (inner ℂ (x : FourierSpace)
      ((shiftedMagneticFourier material c t).toEuclideanLin x)).re < 0 := by
  rw [shifted_energy]
  let y := (frequencyCurl c).conjTranspose.toEuclideanLin (x : FourierSpace)
  have hM : (inner ℂ y ((fourierInverseMass material).toEuclideanLin y)).re ≤ ‖y‖^2 := by
    have hn := (BoxMagnetic.inverseMaterial material).le_opNorm y
    have hb := BoxMagnetic.inverseMaterial_norm material hm
    have hn' : ‖(BoxMagnetic.inverseMaterial material) y‖ ≤ ‖y‖ := by
      exact hn.trans (by simpa using mul_le_mul_of_nonneg_right hb (norm_nonneg y))
    calc
      _ ≤ ‖inner ℂ y ((fourierInverseMass material).toEuclideanLin y)‖ := Complex.re_le_norm _
      _ ≤ ‖y‖ * ‖(BoxMagnetic.inverseMaterial material) y‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖^2 := by nlinarith [norm_nonneg y]
  have hC := orthogonal_curl_bound c x x.property
  have hn : 0 < ‖(x : FourierSpace)‖^2 := sq_pos_of_ne_zero
    (ne_of_gt (norm_pos_iff.mpr (by exact_mod_cast hx)))
  have hstrict := mul_lt_mul_of_pos_right ht hn
  change _ ≤ ‖(frequencyCurl c).conjTranspose.toEuclideanLin (x : FourierSpace)‖^2 at hM
  linarith

theorem orthogonal_negative (material : PeriodicYee.Cell20 → ℝ)
    (hm : ∀ e, 1 ≤ edgeAverage material e) (c : Momentum)
    (hc : ∀ j, |c j| ≤ 1/8) (t : ℝ) (ht : 1/64 - 1/2^24 ≤ t)
    (x : (highSpace c)ᗮ) (hx : x ≠ 0) :
    (inner ℂ (x : FourierSpace)
      ((shiftedMagneticFourier material c t).toEuclideanLin x)).re < 0 :=
  orthogonal_negative_of_low material hm c t ((GammaSymbols.gamma_low c hc).trans_le ht) x hx

theorem high_positive (material : PeriodicYee.Cell20 → ℝ)
    (hm : ∀ e, 1 ≤ edgeAverage material e ∧ edgeAverage material e ≤ 13)
    (c : Momentum) (hc : ∀ j, |c j| ≤ 1/8) (t : ℝ) (ht : t ≤ 1/64 + 1/2^24)
    (x : highSpace c) (hx : x ≠ 0) :
    0 < (inner ℂ (x : FourierSpace)
      ((shiftedMagneticFourier material c t).toEuclideanLin x)).re := by
  have hL (f : Frequency) (hf : f ∈ highFrequencies) :
      (46/100 : ℝ)^2 ≤ laplacianSymbol c f := by
    have hn := GammaSymbols.nonzero_center_norm f (Finset.mem_erase.mp hf).1
    have h := BoxGeometry.longitudinal_norm_shift_lower_uniform 0 c f
      (7/100) (53/100) (GammaSymbols.gamma_displacement c hc) hn
    simp only [zero_add] at h
    have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 53/100-7/100) h 2
    rw [BoxFourierProjection.longitudinalVector_norm_sq] at hs
    convert hs using 1
    norm_num
  have h := shiftedMagneticFourier_high_lower material c highFrequencies 13
    ((46/100)^2) t (by norm_num) (fun e => ⟨by linarith [(hm e).1], (hm e).2⟩)
    hL x x.property
  have hp : 0 < (46/100 : ℝ)^2/13-t := by linarith
  have hn : 0 < ‖(x : FourierSpace)‖^2 := sq_pos_of_ne_zero
    (ne_of_gt (norm_pos_iff.mpr (by exact_mod_cast hx)))
  exact (mul_pos hp hn).trans_le h

/-- Complete Gamma inertia for every threshold in the closed certificate
window, with the origin included. -/
theorem gamma_magnetic_inertia (material : PeriodicYee.Cell20 → ℝ)
    (hm : ∀ e, 1 ≤ edgeAverage material e ∧ edgeAverage material e ≤ 13)
    (c : Momentum) (hc : ∀ j, |c j| ≤ 1/8) (t : ℝ)
    (ht : |t-1/64| ≤ 1/2^24) :
    (Finset.univ.filter fun i =>
      (shiftedMagneticFourier_symmetric material c t).eigenvalues rfl i < 0).card = 2002 ∧
    (Finset.univ.filter fun i =>
      (shiftedMagneticFourier_symmetric material c t).eigenvalues rfl i = 0).card = 0 ∧
    (Finset.univ.filter fun i =>
      0 < (shiftedMagneticFourier_symmetric material c t).eigenvalues rfl i).card = 3998 := by
  have hb := abs_le.mp ht
  have h := inertia_of_complementary_trials
    (shiftedMagneticFourier material c t).toEuclideanLin
    (shiftedMagneticFourier_symmetric material c t)
    (highSpace c)ᗮ.subtype (highSpace c).subtype
    (orthogonal_negative material (fun e => (hm e).1) c hc t (by linarith))
    (high_positive material hm c hc t (by linarith))
    (by rw [highSpace_orthogonal_finrank c hc, highSpace_finrank c hc]
        norm_num [FourierSpace, Electric, Cell])
  simpa only [highSpace_orthogonal_finrank c hc, highSpace_finrank c hc] using h

/-- The actual primitive electric Gamma fiber has precisely 2002 negative
eigenvalues, obtained through the exact electric/magnetic Schur identity. -/
theorem gamma_electric_count (material : PeriodicYee.Cell20 → ℝ)
    (hm : ∀ e, 1 ≤ edgeAverage material e ∧ edgeAverage material e ≤ 13)
    (c : Momentum) (hc : ∀ j, |c j| ≤ 1/8) :
    (Finset.univ.filter fun i =>
      (electricFiber_symmetric material (boundaryMomentum c)).eigenvalues rfl i < 0).card = 2002 := by
  rw [electric_magnetic_physical_negative_count material _
    (fun e => by linarith [(hm e).1]), magneticFiber_fourier_negative_count]
  exact (gamma_magnetic_inertia material hm c hc (1/64) (by norm_num)).1

end Maxwell.Spectral.GammaInertia
