import Maxwell.Continuum.VacuumEncoder
import Maxwell.Continuum.VacuumDecoder
import Maxwell.Continuum.ContractSoundness

/-! Complete execution and quantitative bounds for the unit-vacuum base
instance. The general encoder will reuse `VacuumEncoder.emitCode` after its
source scan has selected this branch. -/

noncomputable section
namespace Maxwell.Continuum.Realization
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private theorem base_cost_budget (C : Constants) (S : Source.SparseSystem)
    (hn : S.n≤S.nnz) (hC : 65000000000≤C.overhead) (cost k : ℕ) (hk : 3≤k)
    (hc : cost≤500000260*(S.n+1)*(S.n.bits.length+2)^3) :
    (cost:ℝ)≤budget C S k := by
  let m := S.effectiveSize
  let l := Parameters.inputLog S.nnz
  have hl : 1≤l := Parameters.inputLog_pos S.nnz
  have hm : 2≤m := le_max_left _ _
  have hn' : S.n+1≤2*m := by
    have h := le_max_right 2 S.nnz
    dsimp [m,Source.SparseSystem.effectiveSize] at *
    omega
  have hb : S.n.bits.length≤l+1 := by
    have h := Codec.unsignedBitLength_mono (hn.trans (Parameters.input_le_binary S.nnz))
    rw [Dyadic.denominator_bitLength] at h
    simpa only [Codec.unsignedBitLength_eq_size,← Nat.size_eq_bits_len] using h
  have hb' : S.n.bits.length+2≤4*l := by omega
  have hnat : cost≤65000000000*m*l^3 := by
    have h := hc.trans (Nat.mul_le_mul
      (Nat.mul_le_mul_left _ hn') (Nat.pow_le_pow_left hb' 3))
    nlinarith only [h,Nat.zero_le (m*l^3)]
  have hmR : (1:ℝ)≤m := by exact_mod_cast (by omega : 1≤m)
  have hlR : (1:ℝ)≤l := by exact_mod_cast hl
  have hpow : (m:ℝ)≤(m:ℝ)^(3/2:ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hmR (by norm_num : (1:ℝ)≤3/2)
  have hcR : (65000000000:ℝ)≤C.overhead := by exact_mod_cast hC
  calc
    (cost:ℝ)≤65000000000*(m:ℝ)*(l:ℝ)^3 := by exact_mod_cast hnat
    _≤(C.overhead:ℝ)*(m:ℝ)^(3/2:ℝ)*(l:ℝ)^k := by
      gcongr
    _=budget C S k := rfl

theorem vacuum_branch (p : Source.Parameters) (C : Constants) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hbase : S.source=0∨S.nnz≤1)
    (hc : 65000000000≤C.overhead) (hw : 4≤C.wordCoefficient)
    (hpower : 10≤C.conditionPower) :
    VacuumBranch p C S VacuumEncoder.program CompleteDecoder.program := by
  have hn := Source.dimension_le_nnz S hp.1
  have he := VacuumEncoder.fuel_le S.n S.n le_rfl
  have hd := VacuumDecoder.cost_le S
  have hb : S.n.bits.length+2≤(S.n.bits.length+2)^3 :=
    le_self_pow₀ (by omega) (by decide : (3:ℕ)≠0)
  have he' : VacuumEncoder.fuel S.n≤260*(S.n+1)*(S.n.bits.length+2)^3 := by
    have hlinear : 100*S.n.bits.length+160≤260*(S.n.bits.length+2)^3 := by
      nlinarith only [hb]
    exact he.trans (by nlinarith only [Nat.mul_le_mul_left (S.n+1) hlinear])
  have hsum : VacuumEncoder.fuel S.n+(CompleteDecoder.vacuumCost (vacuumDecoder S)+1)≤
      500000260*(S.n+1)*(S.n.bits.length+2)^3 := by nlinarith only [he',hd]
  have hlen : (vacuumBytes S).length≤500000260*(S.n+1)*(S.n.bits.length+2)^3 := by
    have h := VacuumDecoder.description_length S
    have hp1 : 1≤(S.n+1)*(S.n.bits.length+2)^3 :=
      Nat.mul_pos (by omega) (pow_pos (by omega) _)
    have hprod := Nat.mul_le_mul_left (16*(S.n+1)) hb
    simp only [vacuumBytes,List.length_cons]
    nlinarith only [h,hp1,hprod]
  have hunit : (1:ℝ)≤budget C S 24 := by
    have hpos : 1≤(S.n+1)*(S.n.bits.length+2)^3 :=
      Nat.mul_pos (by omega) (pow_pos (by omega) _)
    have hnat : 1≤500000260*(S.n+1)*(S.n.bits.length+2)^3 := by nlinarith only [hpos]
    simpa only [Nat.cast_one] using base_cost_budget C S hn hc 1 24 (by decide) hnat
  refine ⟨VacuumEncoder.fuel S.n,CompleteDecoder.vacuumCost (vacuumDecoder S)+1,
    VacuumEncoder.encodes S,VacuumDecoder.decodes S C hw,
    base_cost_budget C S hn hc _ 4096 (by decide) hsum,
    base_cost_budget C S hn hc _ 64 (by decide) hlen,?_,?_,?_,
    VacuumBox.inverse_norm,vacuum_condition C S hpower,vacuum_recovery p S hp.1 hbase⟩
  · simpa only [VacuumBox.physical_volume] using hunit
  · simp [vacuumDecoder,Target.FixedPointFormat.width,wordBudget]
    have hl := Parameters.inputLog_pos S.nnz
    nlinarith only [hw,hl]
  · have hm : (1:ℝ)≤S.effectiveSize := by
      exact_mod_cast (show 1≤S.effectiveSize from (by decide : 1≤2).trans (le_max_left _ _))
    rw [VacuumBox.tolerance,Rat.cast_one]
    exact Real.rpow_le_one_of_one_le_of_nonpos hm (neg_nonpos.mpr (Nat.cast_nonneg _))

#print axioms vacuum_branch

end Maxwell.Continuum.Realization
