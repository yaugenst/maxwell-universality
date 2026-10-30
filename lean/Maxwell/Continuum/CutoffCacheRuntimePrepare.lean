import Maxwell.Continuum.CutoffCacheDimensions

/-! The cutoff cache derives its degree and layout from the producer's
runtime precision, actual input width header, and computed free-memory cursor. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768

def cacheLoadIds : Finset ℕ := cacheDimensionIds∪{200,660,709}
def cacheLoadInput (N W heap : ℕ) (i : ℕ) : ℕ :=
  if i=200 then W else if i=660 then N else if i=709 then heap else 0

def cacheLoadPlan : List NatAssign.Instruction :=
  [.copy 660 720,.literal 728 256,.add 728 720,.literal 728 128,.multiply 728 720,
   .copy 720 728,.multiply 728 720,.copy 200 721,.copy 709 722,.literal 728 0]

def cacheLoadValues (N W heap : ℕ) : ℕ→ℕ := NatAssign.values cacheLoadPlan (cacheLoadInput N W heap)
def cacheRuntimePrepareCode : Code := .seq (NatAssign.code cacheLoadPlan) cacheDimensionCode

def cacheRuntimePrepareCost (B : ℕ) : ℕ := stageCost B+cacheDimensionCost (2^11*(B+1))

theorem cacheLoadPlan_valid : ∀a∈cacheLoadPlan,a.Valid cacheLoadIds := by
  simp [cacheLoadPlan,NatAssign.Instruction.Valid,cacheLoadIds,cacheDimensionIds]

theorem cacheLoadValues_eq (N W heap i : ℕ) (hi : i∈cacheDimensionIds) :
    cacheLoadValues N W heap i=cacheDimensionInput (Profile.profileDegree N) W heap i := by
  by_cases h : i∈({720,721,722,728}:Finset ℕ)
  · simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl|rfl|rfl|rfl <;>
      simp [cacheLoadValues,cacheLoadPlan,NatAssign.values,NatAssign.Instruction.update,
        NatAssign.Instruction.target,NatAssign.Instruction.value,cacheLoadInput,cacheDimensionInput,
        Profile.profileDegree]
    all_goals ring
  · simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at h
    rw [cacheLoadValues,values_unchanged cacheLoadPlan _ i (by
      simp [cacheLoadPlan,NatAssign.Instruction.target];omega)]
    have hr := Finset.mem_Icc.mp hi
    simp [cacheLoadInput,cacheDimensionInput,h.1,h.2.1,h.2.2.1,
      show i≠200 by omega,show i≠660 by omega,show i≠709 by omega]

theorem cacheLoad_width (N W heap B : ℕ) (hB : 9≤B)
    (hN : N.bits.length≤B) (hW : W.bits.length≤B) (hh : heap.bits.length≤B)
    (i : ℕ) (hi : i∈cacheLoadIds) : (cacheLoadValues N W heap i).bits.length≤2^11*(B+1) := by
  have hin (i : ℕ) (_hi : i∈cacheLoadIds) : (cacheLoadInput N W heap i).bits.length≤B := by
    unfold cacheLoadInput
    split_ifs <;> first | exact hN | exact hW | exact hh | simp
  have lit : ∀a∈cacheLoadPlan,a.literalWidth≤B := by
    simp [cacheLoadPlan,NatAssign.Instruction.literalWidth,
      show (256:ℕ).bits.length=9 from rfl,show (128:ℕ).bits.length=8 from rfl]
    omega
  have h := NatAssign.values_width_bound cacheLoadIds cacheLoadPlan cacheLoadPlan_valid
    (cacheLoadInput N W heap) B hin lit i hi
  change (cacheLoadValues N W heap i).bits.length+1≤2^10*(B+1) at h
  omega

theorem cacheRuntimePrepare_executes (N W heap B : ℕ) (hB : 9≤B)
    (hN : N.bits.length≤B) (hW : W.bits.length≤B) (hh : heap.bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank cacheLoadIds (cacheLoadInput N W heap) s.val)
    (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape cacheRuntimePrepareCode cost s t ∧ cost≤cacheRuntimePrepareCost B ∧
      NatAssign.Bank cacheDimensionIds (cacheDimensionValues (Profile.profileDegree N) W heap) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame ({0,1,2,3}∪cacheDimensionIds) s.val t.val := by
  have ge (i : ℕ) (hi : i∈cacheLoadIds) : 4 ≤ i := by
    simp only [cacheLoadIds,cacheDimensionIds,Finset.mem_union,Finset.mem_Icc,
      Finset.mem_insert,Finset.mem_singleton] at hi;omega
  obtain ⟨c0,s0,e0,hc0,b0,z0,f0⟩ := NatAssign.executes cacheLoadIds ge cacheLoadPlan cacheLoadPlan_valid
    (cacheLoadInput N W heap) input tape s hs hz
  have hin (i : ℕ) (_hi : i∈cacheLoadIds) : (cacheLoadInput N W heap i).bits.length≤B := by
    unfold cacheLoadInput
    split_ifs <;> first | exact hN | exact hW | exact hh | simp
  have lit : ∀a∈cacheLoadPlan,a.literalWidth≤B := by
    simp [cacheLoadPlan,NatAssign.Instruction.literalWidth,
      show (256:ℕ).bits.length=9 from rfl,show (128:ℕ).bits.length=8 from rfl]
    omega
  have hp := NatAssign.price_bound cacheLoadIds cacheLoadPlan cacheLoadPlan_valid
    (cacheLoadInput N W heap) B hin lit
  have price : c0≤stageCost B := by
    apply hc0.trans (hp.trans _)
    change 3000*8^10*(B+2)^2≤2^96*(B+2)^2
    exact Nat.mul_le_mul_right _ (by norm_num)
  have bank : NatAssign.Bank cacheDimensionIds (cacheDimensionInput (Profile.profileDegree N) W heap) s0.val := by
    intro i hi
    have h := b0 i (Finset.mem_union_left _ hi)
    change RationalAccumulator.Word s0.val i (cacheLoadValues N W heap i) at h
    simpa only [cacheLoadValues_eq N W heap i hi] using h
  have width (i : ℕ) (hi : i∈cacheDimensionIds) :
      (cacheDimensionInput (Profile.profileDegree N) W heap i).bits.length≤2^11*(B+1) := by
    rw [←cacheLoadValues_eq N W heap i hi]
    exact cacheLoad_width N W heap B hB hN hW hh i (Finset.mem_union_left _ hi)
  obtain ⟨c1,t,e1,hc1,b1,z1,f1⟩ := cacheDimension_executes (Profile.profileDegree N) W heap
    (2^11*(B+1)) (by omega) (by simpa [cacheDimensionInput] using width 720 (by decide))
    (by simpa [cacheDimensionInput] using width 721 (by decide))
    (by simpa [cacheDimensionInput] using width 722 (by decide)) input tape s0 bank z0
  exact ⟨c0+c1,t,e0.seq e1,by unfold cacheRuntimePrepareCost;omega,b1,z1,
    (f0.mono (by decide)).trans f1⟩

theorem cacheRuntimePrepareCost_polynomial (B : ℕ) :
    cacheRuntimePrepareCost B≤2^170*(B+2)^2 := by
  have h := cacheDimensionCost_polynomial (2^11*(B+1))
  have hp : (2^11*(B+1)+2)^2≤(2^12*(B+2))^2 := Nat.pow_le_pow_left (by omega) 2
  have hq : cacheDimensionCost (2^11*(B+1))≤2^168*(B+2)^2 := by
    calc
      _≤2^144*(2^11*(B+1)+2)^2 := h
      _≤2^144*(2^12*(B+2))^2 := Nat.mul_le_mul_left _ hp
      _=_ := by ring
  unfold cacheRuntimePrepareCost stageCost
  omega

#print axioms cacheRuntimePrepare_executes
#print axioms cacheRuntimePrepareCost_polynomial
end Maxwell.Continuum.Calibration.RawCutoff
