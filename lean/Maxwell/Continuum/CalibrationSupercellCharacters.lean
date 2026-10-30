import Maxwell.Continuum.CalibrationSupercellIndex
import Maxwell.Continuum.PeriodicSamplingReconstruction
import Maxwell.Continuum.CellSourceTranslation
import Maxwell.Continuum.CellBlochWave

/-! Exact grid characters and physical cell phases, including the
antiperiodic carrier in the supercell Fourier decomposition. -/

noncomputable section

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellBandFourier CellGauge UnitAddTorus PeriodicSampling

variable (M : ℕ) [NeZero M]

theorem character_comm (a j : Grid M) : Product.character M a j=Product.character M j a := by
  unfold Product.character
  apply Finset.prod_congr rfl
  intro i _
  rw [mul_comm]

theorem character_zero (j : Grid M) : Product.character M 0 j=1 := by
  simp [Product.character,AddChar.map_zero_eq_one]

theorem character_conj (a j : Grid M) :
    star (Product.character M a j)=Product.character M (-a) j := by
  rw [Complex.star_def,← Complex.inv_eq_conj (Product.character_norm M a j)]
  simp only [Product.character,Pi.neg_apply,neg_mul,AddChar.map_neg_eq_inv,Finset.prod_inv_distrib]

theorem character_orthogonality (j k : Grid M) :
    (∑ a : Grid M, star (Product.character M a j)*Product.character M a k)=
      if j=k then (M : ℂ)^3 else 0 := by
  classical
  simp_rw [character_comm M,character_conj M,Product.character_mul]
  have he : -j+k=0 ↔ j=k := by
    constructor
    · intro h
      have hh := congrArg (fun x : Grid M => j+x) h
      simpa only [← add_assoc,add_neg_cancel,zero_add,add_zero] using hh.symm
    · intro h
      rw [h,neg_add_cancel]
  have hc := Product.character_sum M (-j+k)
  simp only [Fintype.card_fin,he] at hc
  convert hc using 1
  congr 1
  ext a
  simp only [Finset.mem_univ]

theorem centered_character (a : Alias) (j : Grid M) :
    Product.phase a (fun i => (centeredGrid M (j i) : ℝ))=
      Product.character M (Product.frequency M a) j := by
  rw [Product.phase_monomial]
  have he : (fun i => ((centeredGrid M (j i) : ℝ) : UnitAddCircle))=
      fun i => (((j i).val : ℝ)/(M : ℝ) : UnitAddCircle) := by
    funext i
    exact centeredGrid_coe M (j i)
  rw [he,← Product.phase_monomial]
  exact Product.phase_grid M a j

def momentum (j : Grid M) : Momentum := realMomentum (fun i => Real.pi*(centeredGrid M (j i) : ℝ))

def cellPhase (j : Grid M) (a : Alias) : ℂ :=
  carrier (latticeShift a)*Product.character M (Product.frequency M a) j

theorem momentum_lattice_phase (j : Grid M) (a : Alias) :
    spatialPhase (momentum M j) (latticeShift a)=Product.character M (Product.frequency M a) j := by
  rw [← centered_character]
  simp only [spatialPhase,momentum,realMomentum,latticeShift,Bloch.integerVector_apply,
    PiLp.smul_apply,smul_eq_mul,Product.phase,PeriodicSampling.phase,Fin.prod_univ_three,
    Fin.sum_univ_three,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_intCast]
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  ring

theorem cellPhase_norm (j : Grid M) (a : Alias) : ‖cellPhase M j a‖=1 := by
  rw [cellPhase,norm_mul,carrier_norm,Product.character_norm,one_mul]

theorem alias_lattice_phase (j : Grid M) (a ν : Alias) :
    spatialPhase (aliasMomentum (momentum M j) ν) (latticeShift a)=cellPhase M j a := by
  rw [aliasMomentum_add,spatialPhase_add,← aliasPhase_eq,momentum_lattice_phase]
  have ht : torusPoint (latticeShift a)=0 := by
    funext i
    change (((2*(a i : ℝ))/2 : ℝ) : UnitAddCircle)=0
    rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ)≠0)]
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨a i,by simp⟩
  have hz : mFourier ν (0 : Torus)=1 := by simp [mFourier,fourier_apply]
  rw [ht,hz,mul_one,cellPhase]
  exact mul_comm _ _

theorem join_momentum (hEven : Even M) (j : Grid M) (ν : Alias) :
    realMomentum (fun i => Real.pi*(join M (j,ν) i : ℝ)/(M : ℝ))=aliasMomentum (momentum M j) ν := by
  funext i
  change ((Real.pi*(join M (j,ν) i : ℝ)/(M : ℝ) : ℝ) : ℂ)=_
  rw [join_wavevector M hEven]
  simp only [realMomentum,aliasMomentum,momentum,Complex.ofReal_mul,
    Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,Complex.ofReal_intCast]
  ring

theorem join_cell_phase (hEven : Even M) (j : Grid M) (ν a : Alias) (x : Space) :
    spatialPhase (realMomentum (fun i => Real.pi*(join M (j,ν) i : ℝ)/(M : ℝ))) (latticeShift a+x)=
      cellPhase M j a*(spatialPhase (momentum M j) x*(carrier x*mFourier ν (torusPoint x))) := by
  rw [join_momentum M hEven,spatialPhase_space_add,alias_lattice_phase,
    aliasMomentum_add,spatialPhase_add,← aliasPhase_eq]

#print axioms character_orthogonality
#print axioms join_cell_phase

end Maxwell.Continuum.Calibration.Supercell
