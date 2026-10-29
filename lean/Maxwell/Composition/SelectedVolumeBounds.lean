import Maxwell.Composition.SelectedDimensionBounds
import Maxwell.Cost.Ambient

/-! The complete buffered box retains the three-halves source-size exponent.
Every scalar cell and retained electric edge is counted, including empty
space; only powers of the logarithm are spent on spacing and buffering. -/
noncomputable section
namespace Maxwell.Composition.SelectedVolumeBounds
open Maxwell.Realization Maxwell.Composition.SelectedLogicalBounds
open Maxwell.Composition.SelectedSpacingBounds Maxwell.Composition.SelectedBufferBounds
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1500000

def logFactor (m : ℕ) : ℝ := 1+Real.log (m:ℝ)
def precisionCoefficient (p : Source.Parameters) : ℝ :=
  8+(⌈p.conditionExponent⌉₊+⌈p.accuracyExponent⌉₊+2 : ℕ)+
    (⌈p.conditionExponent⌉₊+⌈p.accuracyExponent⌉₊+2 : ℕ)/Real.log 2
def distanceCoefficient (p : Source.Parameters) (R : SelectedPlatform) : ℝ :=
  distanceBase R+distanceSlope p R+(distanceSlope p R:ℝ)/Real.log 2
def frameCoefficient (p : Source.Parameters) (R : SelectedPlatform) : ℝ :=
  distanceCoefficient p R+coefficient p R+1
def volumeCoefficient (p : Source.Parameters) (R : SelectedPlatform) : ℝ :=
  (R.physical.volumeCoefficient:ℝ)*(frameCoefficient p R)^3*
    (64*(30*precisionCoefficient p)^(3/2:ℝ))

theorem logFactor_ge_one (m : ℕ) (hm : 0 < m) : 1 ≤ logFactor m := by
  have h := Real.log_nonneg (show (1:ℝ)≤m by exact_mod_cast hm)
  unfold logFactor
  linarith

theorem precisionCoefficient_pos (p : Source.Parameters) : 0 < precisionCoefficient p := by
  have h := Real.log_pos (by norm_num : (1:ℝ)<2)
  unfold precisionCoefficient
  positivity

theorem distanceCoefficient_nonneg (p : Source.Parameters) (R : SelectedPlatform) :
    0 ≤ distanceCoefficient p R := by
  have h := Real.log_pos (by norm_num : (1:ℝ)<2)
  unfold distanceCoefficient
  positivity

theorem frameCoefficient_pos (p : Source.Parameters) (R : SelectedPlatform) :
    0 < frameCoefficient p R := by
  have h := distanceCoefficient_nonneg p R
  have h' := coefficient_pos p R
  unfold frameCoefficient
  positivity

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) (R : SelectedPlatform)
local notation "I" => SelectedInput.input p S hm

theorem precision_log_bound : ((I).precision:ℝ)+1 ≤ precisionCoefficient p*logFactor S.nnz := by
  have h := binaryCoefficientPrecision_le_log S.nnz ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ hm
  have hl : 0 ≤ Real.log (S.nnz:ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have hlog := Real.log_pos (by norm_num : (1:ℝ)<2)
  change ((I).precision:ℝ) ≤ _ at h
  have he : ((⌈p.conditionExponent⌉₊+⌈p.accuracyExponent⌉₊+2:ℕ):ℝ)*
      (1+Real.log (S.nnz:ℝ)/Real.log 2) =
      (⌈p.conditionExponent⌉₊+⌈p.accuracyExponent⌉₊+2:ℕ)+
        (((⌈p.conditionExponent⌉₊+⌈p.accuracyExponent⌉₊+2:ℕ):ℝ)/Real.log 2)*Real.log (S.nnz:ℝ) := by ring
  rw [he] at h
  dsimp only [precisionCoefficient,logFactor]
  have ha : (0:ℝ)≤(⌈p.conditionExponent⌉₊+⌈p.accuracyExponent⌉₊+2:ℕ) := by positivity
  nlinarith [div_nonneg ha hlog.le, mul_nonneg ha hl]

theorem distance_log_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    ((I).distance R:ℝ) ≤ distanceCoefficient p R*logFactor S.nnz := by
  have hd : ((I).distance R:ℝ) ≤ (distanceBase R:ℝ)+(distanceSlope p R:ℝ)*Nat.clog 2 S.nnz := by
    exact_mod_cast distance_bound p S hm R hm2 hunit
  have hc : Nat.clog 2 S.nnz ≤ S.nnz.size := Nat.clog_le_of_le_pow (Nat.lt_size_self _).le
  have hcR : (Nat.clog 2 S.nnz:ℝ) ≤ 1+Real.log (S.nnz:ℝ)/Real.log 2 :=
    (by exact_mod_cast hc : (Nat.clog 2 S.nnz:ℝ) ≤ S.nnz.size).trans (nat_size_le_real_log _ hm)
  have h := hd.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcR (by positivity)))
  have hl : 0 ≤ Real.log (S.nnz:ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have hlog := Real.log_pos (by norm_num : (1:ℝ)<2)
  have he : (distanceSlope p R:ℝ)*(1+Real.log (S.nnz:ℝ)/Real.log 2) =
      (distanceSlope p R:ℝ)+((distanceSlope p R:ℝ)/Real.log 2)*Real.log (S.nnz:ℝ) := by ring
  rw [he] at h
  dsimp only [distanceCoefficient,logFactor]
  nlinarith [Nat.cast_nonneg (α:=ℝ) (distanceBase R), Nat.cast_nonneg (α:=ℝ) (distanceSlope p R),
    div_nonneg (Nat.cast_nonneg (α:=ℝ) (distanceSlope p R)) hlog.le,
    mul_nonneg (Nat.cast_nonneg (α:=ℝ) (distanceBase R)) hl,
    mul_nonneg (Nat.cast_nonneg (α:=ℝ) (distanceSlope p R)) hl]

theorem side_cube_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (SourceRouting.side S (I).precision:ℝ)^3 ≤
      (64*(30*precisionCoefficient p)^(3/2:ℝ))*(S.nnz:ℝ)^(3/2:ℝ)*(logFactor S.nnz)^2 := by
  have hc := Maxwell.Logical.sourceCircuit_size_two_le S hm2 (I).precision
  have hv : 0 < Fintype.card (SourcePositive.Vertex S (I).precision) := by
    change 0 < Fintype.card ((Fin _ ⊕ Fin _) ⊕ _)
    simp only [Fintype.card_sum,Fintype.card_fin]
    omega
  have hq := Maxwell.Cost.portSide_cube_bound _ hv
  change (SourceRouting.side S (I).precision:ℝ)^3 ≤ _ at hq
  have hu : (Fintype.card (SourcePositive.Vertex S (I).precision):ℝ) ≤
      30*(S.nnz:ℝ)*((I).precision+1) := by
    exact_mod_cast SourceRouting.original_vertices_le S (I).precision (Source.dimension_le_nnz S hunit)
  have hU := hu.trans (mul_le_mul_of_nonneg_left (precision_log_bound p S hm) (by positivity))
  have hp := precisionCoefficient_pos p
  have hl := logFactor_ge_one S.nnz hm
  have hr := Real.rpow_le_rpow (by positivity) hU (by norm_num : (0:ℝ)≤3/2)
  have hexp : (30*(S.nnz:ℝ)*(precisionCoefficient p*logFactor S.nnz))^(3/2:ℝ) =
      (30*precisionCoefficient p)^(3/2:ℝ)*(S.nnz:ℝ)^(3/2:ℝ)*(logFactor S.nnz)^(3/2:ℝ) := by
    have he : 30*(S.nnz:ℝ)*(precisionCoefficient p*logFactor S.nnz) =
        (30*precisionCoefficient p)*(S.nnz:ℝ)*logFactor S.nnz := by ring
    rw [he, Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
  rw [hexp] at hr
  have hlpow : (logFactor S.nnz)^(3/2:ℝ) ≤ (logFactor S.nnz)^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hl (by norm_num : (3/2:ℝ)≤2)
  calc
    _ ≤ 64*((30*precisionCoefficient p)^(3/2:ℝ)*(S.nnz:ℝ)^(3/2:ℝ)*(logFactor S.nnz)^(3/2:ℝ)) :=
      hq.trans (mul_le_mul_of_nonneg_left hr (by norm_num))
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left hlpow
        (show (0:ℝ)≤64*(30*precisionCoefficient p)^(3/2:ℝ)*(S.nnz:ℝ)^(3/2:ℝ) by positivity)
        using 1
      ring

theorem feedback_log_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S))
    (count : ℕ)
    (hcount : (count:ℝ) ≤ (R.physical.volumeCoefficient:ℝ)*
      ((((I).distance R*SourceRouting.side S (I).precision:ℕ):ℝ)+(buffer p S hm R:ℝ)+1)^3) :
    (count:ℝ) ≤
      volumeCoefficient p R*(S.nnz:ℝ)^(3/2:ℝ)*(logFactor S.nnz)^5 := by
  have hd := distance_log_bound p S hm R hm2 hunit
  have hb := logarithmic p S hm R hm2 hunit
  have hq : (1:ℝ) ≤ SourceRouting.side S (I).precision := by
    exact_mod_cast SourceRouting.side_pos S (I).precision
  have hl := logFactor_ge_one S.nnz hm
  have hf : ((I).distance R:ℝ)+(buffer p S hm R:ℝ)+1 ≤ frameCoefficient p R*logFactor S.nnz := by
    change _ ≤ coefficient p R*logFactor S.nnz at hb
    unfold frameCoefficient
    nlinarith
  have hs : (((I).distance R*SourceRouting.side S (I).precision:ℕ):ℝ)+(buffer p S hm R:ℝ)+1 ≤
      (SourceRouting.side S (I).precision:ℝ)*(frameCoefficient p R*logFactor S.nnz) := by
    push_cast
    have h := mul_le_mul_of_nonneg_left hf (by positivity : (0:ℝ)≤SourceRouting.side S (I).precision)
    nlinarith [mul_le_mul_of_nonneg_right hq (show (0:ℝ)≤(buffer p S hm R:ℝ)+1 by positivity)]
  have hc := pow_le_pow_left₀ (by positivity) hs 3
  have hv : (0:ℝ) ≤ R.physical.volumeCoefficient := by exact_mod_cast R.physical.volumeCoefficient_nonneg
  have hN := hcount.trans (mul_le_mul_of_nonneg_left hc hv)
  have hcube := side_cube_bound p S hm hm2 hunit
  have hf0 := (frameCoefficient_pos p R).le
  calc
    _ ≤ (R.physical.volumeCoefficient:ℝ)*(SourceRouting.side S (I).precision:ℝ)^3*
        (frameCoefficient p R)^3*(logFactor S.nnz)^3 := by
      convert hN using 1
      ring
    _ ≤ (R.physical.volumeCoefficient:ℝ)*
        ((64*(30*precisionCoefficient p)^(3/2:ℝ))*(S.nnz:ℝ)^(3/2:ℝ)*(logFactor S.nnz)^2)*
        (frameCoefficient p R)^3*(logFactor S.nnz)^3 := by gcongr
    _ = _ := by unfold volumeCoefficient; ring

theorem dimension_log_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (Fintype.card ((I).box R).Edge:ℝ) ≤
      volumeCoefficient p R*(S.nnz:ℝ)^(3/2:ℝ)*(logFactor S.nnz)^5 := by
  apply feedback_log_bound p S hm R hm2 hunit
  exact R.physical.physical_edge_feedback S (I).precision ((I).distance R) (buffer p S hm R)

theorem cells_log_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (Fintype.card ((I).box R).Cell:ℝ) ≤
      volumeCoefficient p R*(S.nnz:ℝ)^(3/2:ℝ)*(logFactor S.nnz)^5 := by
  apply feedback_log_bound p S hm R hm2 hunit
  let b := buffer p S hm R
  let bound := R.physical.boxCoefficient*((I).distance R*SourceRouting.side S (I).precision+b+1)
  have h0 := R.physical.physical_side_feedback S (I).precision ((I).distance R) b 0
  have h1 := R.physical.physical_side_feedback S (I).precision ((I).distance R) b 1
  have h2 := R.physical.physical_side_feedback S (I).precision ((I).distance R) b 2
  change ((I).box R).nx ≤ bound at h0
  change ((I).box R).ny ≤ bound at h1
  change ((I).box R).nz ≤ bound at h2
  have hc : Fintype.card ((I).box R).Cell ≤ bound^3 := by
    change Fintype.card (Fin _ × Fin _ × Fin _) ≤ _
    simp only [Fintype.card_prod,Fintype.card_fin]
    calc
      _ ≤ bound*(bound*bound) := Nat.mul_le_mul h0 (Nat.mul_le_mul h1 h2)
      _ = _ := by ring
  have hcR : (Fintype.card ((I).box R).Cell:ℝ) ≤ (bound:ℝ)^3 := by exact_mod_cast hc
  have h3 : (bound:ℝ)^3 ≤ 3*(bound:ℝ)^3 := by nlinarith [pow_nonneg (Nat.cast_nonneg (α:=ℝ) bound) 3]
  apply (hcR.trans h3).trans_eq
  simp only [bound,b,PhysicalPlatform.volumeCoefficient,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
    Rat.cast_mul,Rat.cast_ofNat,Rat.cast_pow,Rat.cast_natCast]
  ring

def logConversion : ℝ := 1+1/Real.log 2
def overhead (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  ⌈volumeCoefficient p R*logConversion^5⌉₊

theorem logFactor_le_log (m : ℕ) (hm : 0 < m) :
    logFactor m ≤ logConversion*Real.log (2+(m:ℝ)) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hlog := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hlarge : Real.log 2 ≤ Real.log (2+(m:ℝ)) := Real.log_le_log (by norm_num) (by linarith)
  have hsmall : Real.log (m:ℝ) ≤ Real.log (2+(m:ℝ)) := Real.log_le_log hm0 (by linarith)
  have hdiv : 1 ≤ Real.log (2+(m:ℝ))/Real.log 2 := (le_div_iff₀ hlog).mpr (by simpa using hlarge)
  unfold logFactor logConversion
  have he : (1+1/Real.log 2)*Real.log (2+(m:ℝ)) =
      Real.log (2+(m:ℝ))+Real.log (2+(m:ℝ))/Real.log 2 := by ring
  rw [he]
  linarith

theorem count_sizeBudget (C : Constants) (n : ℕ) (hm2 : 2 ≤ S.nnz)
    (hcount : (n:ℝ) ≤ volumeCoefficient p R*(S.nnz:ℝ)^(3/2:ℝ)*(logFactor S.nnz)^5)
    (hC : overhead p R ≤ C.overhead) (hlog : C.logPower = 5) :
    (n:ℝ) ≤ sizeBudget C S := by
  have hm : 0 < S.nnz := by omega
  have hf := logFactor_le_log S.nnz hm
  have hf0 := (logFactor_ge_one S.nnz hm).trans' (by norm_num : (0:ℝ)≤1)
  have hv : (0:ℝ) ≤ volumeCoefficient p R := by
    have h := frameCoefficient_pos p R
    have hp := precisionCoefficient_pos p
    have h' : (0:ℝ) ≤ R.physical.volumeCoefficient := by exact_mod_cast R.physical.volumeCoefficient_nonneg
    unfold volumeCoefficient
    positivity
  have hpow := pow_le_pow_left₀ hf0 hf 5
  have hupper := hcount.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  have hc : volumeCoefficient p R*logConversion^5 ≤ (C.overhead:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hC)
  have hlog0 : 0 ≤ Real.log (2+(S.nnz:ℝ)) := Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) S.nnz; linarith)
  rw [sizeBudget,hlog,effectiveSize,max_eq_right hm2]
  calc
    _ ≤ (volumeCoefficient p R*logConversion^5)*(S.nnz:ℝ)^(3/2:ℝ)*
        (Real.log (2+(S.nnz:ℝ)))^5 := by convert hupper using 1; ring
    _ ≤ _ := by gcongr

end Maxwell.Composition.SelectedVolumeBounds
