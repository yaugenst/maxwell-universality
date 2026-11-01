import Maxwell.Continuum.CalibrationBasisForcingStore
import Maxwell.Continuum.RationalDataflowResetNaturalBank
import Maxwell.Cost.Structured.NatAssign.Values
import Maxwell.Continuum.NaturalBankStageParts

/-! Reset the per-entry workspace before decoding the next forcing row.
Its resulting width depends only on retained inputs and the radius, so array
generation does not multiply the arithmetic width at every iteration. -/
namespace Maxwell.Continuum.Calibration.BasisForcing
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
open ArrayDecodeMachine
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

def retained : Finset ℕ := Finset.range 32 \ {13,14,15,23}
def clearRegisters : List ℕ := (List.range 232).filter (fun k => decide (k∉retained))
def clearedParts (v : ℕ → Parts) : ℕ → Parts := (RationalDataflow.resetList clearRegisters).evaluate v
def clearNaturalWords : List ℕ := [220,221,222,223,310,312,313,314,315,316,317,318,319,320]
def clearPlan : List NatAssign.Instruction := clearNaturalWords.map (fun k => .literal k 0)
def resetNaturalBase (n : ℕ → ℕ) (v : ℕ → Parts) (k : ℕ) : ℕ :=
  if k∈ids bank then dataValues (clearedParts v) k else n k
def clearedNaturals (n : ℕ → ℕ) (v : ℕ → Parts) : ℕ → ℕ :=
  NatAssign.values clearPlan (resetNaturalBase n v)
def resetCode : Code := .seq (RationalDataflow.resetList clearRegisters).code (NatAssign.code clearPlan)
attribute [local irreducible] bank clearRegisters RationalDataflow.resetList

theorem clearRegisters_mem (k : ℕ) : k∈clearRegisters ↔ k∈bank ∧ k∉retained := by
  simp only [clearRegisters,List.mem_filter,List.mem_range,decide_eq_true_eq,bank,Finset.mem_range]

theorem clearedParts_keep (v : ℕ → Parts) (k : ℕ) (hk : k∈retained) : clearedParts v k=v k := by
  rw [clearedParts,resetList_values,ite_eq_right]
  intro h
  exact (clearRegisters_mem k).mp h |>.2 hk

theorem clearedParts_width (v : ℕ → Parts) (B : ℕ) (hB : 1≤B)
    (hv : ∀k∈retained,(v k).Width B) : WidthBank bank B (clearedParts v) := by
  apply resetList_result_width bank clearRegisters v B hB
  intro k hk hc
  have hr : k∈retained := by
    by_contra hn
    exact hc ((clearRegisters_mem k).mpr ⟨hk,hn⟩)
  exact hv k hr

theorem clearNatural_mem (k : ℕ) (hk : k∈clearNaturalWords) :
    k∈naturalIds ∧ k∉ids bank ∧ k≠311 := by
  have h : (k∈NaturalQuotient.workPorts ∨ k∈ArrayDecodeMachine.ports) ∧ k<1000 ∧
      k∉workPorts ∧ k≠311 := by
    simp only [clearNaturalWords,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  exact ⟨h.1.elim (fun hh => naturalIds_work hh) (fun hh => naturalIds_decode hh),
    outside_bank k h.2.1 h.2.2.1,h.2.2.2⟩

theorem clearedNaturals_apply (n : ℕ → ℕ) (v : ℕ → Parts) (k : ℕ) :
    clearedNaturals n v k=if k∈clearNaturalWords then 0 else resetNaturalBase n v k :=
  NatAssign.values_literals clearNaturalWords (fun _ => 0) (resetNaturalBase n v) k

theorem clearedNaturals_agrees (n : ℕ → ℕ) (v : ℕ → Parts) (k : ℕ) (hk : k∈ids bank) :
    clearedNaturals n v k=dataValues (clearedParts v) k := by
  have outside : k∉clearNaturalWords := fun hc => (clearNatural_mem k hc).2.1 hk
  rw [clearedNaturals_apply,ite_eq_right outside,resetNaturalBase,ite_eq_left hk]

theorem clearedNaturals_radius (n : ℕ → ℕ) (v : ℕ → Parts) : clearedNaturals n v 311=n 311 := by
  rw [clearedNaturals_apply,ite_eq_right (by decide : 311∉clearNaturalWords),resetNaturalBase,
    ite_eq_right (outside_bank 311 (by decide) (by decide))]

theorem clearedNaturals_work (n : ℕ → ℕ) (v : ℕ → Parts) (k : ℕ)
    (hk : k∈NaturalQuotient.workPorts) : clearedNaturals n v k=0 := by
  have hc : k∈clearNaturalWords := by
    simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hk
    simp only [clearNaturalWords,List.mem_cons,List.not_mem_nil,or_false]
    tauto
  rw [clearedNaturals_apply,ite_eq_left hc]

theorem clearedNaturals_width (n : ℕ → ℕ) (v : ℕ → Parts) (B : ℕ) (hB : 1≤B)
    (hv : ∀k∈retained,(v k).Width B) (hR : (n 311).bits.length≤B) :
    ∀k∈naturalIds,(clearedNaturals n v k).bits.length≤B := by
  intro k hk
  by_cases hp : k∈ids bank
  · rw [clearedNaturals_agrees n v k hp]
    exact dataValues_width bank _ B (clearedParts_width v B hB hv) k hp
  · by_cases hr : k=311
    · subst k
      rw [clearedNaturals_radius]
      exact hR
    · have hc : k∈clearNaturalWords := by
        rcases Finset.mem_union.mp hk with hk|hk
        · rcases Finset.mem_union.mp hk with hk|hk
          · exact False.elim (hp hk)
          · simp only [ArrayDecodeMachine.ports,Finset.mem_Icc] at hk
            simp only [clearNaturalWords,List.mem_cons,List.not_mem_nil,or_false]
            omega
        · simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hk
          simp only [clearNaturalWords,List.mem_cons,List.not_mem_nil,or_false]
          tauto
      rw [clearedNaturals_apply,ite_eq_left hc]
      simp

theorem reset_executes (n : ℕ → ℕ) (v : ℕ → Parts) (U B : ℕ) (hB : 1≤B) (hBU : B≤U)
    (hn : ∀k∈ids bank,n k=dataValues v k) (hw : ∀k∈naturalIds,(n k).bits.length≤U)
    (hg : Good bank v) (hv : ∀k∈retained,(v k).Width B) (hR : (n 311).bits.length≤B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : NatAssign.Bank naturalIds n s.val)
    (hz : ∀k,k<5 → RationalAccumulator.Blank s.val k) :
    ∃cost t,Executes input tape resetCode cost s t ∧ cost≤2^110*(U+3)^2 ∧
      Ready bank (clearedParts v) t ∧ Good bank (clearedParts v) ∧ WidthBank bank B (clearedParts v) ∧
      NatAssign.Bank naturalIds (clearedNaturals n v) t.val ∧
      (∀k∈naturalIds,(clearedNaturals n v k).bits.length≤B) ∧
      (∀k,k<5 → RationalAccumulator.Blank t.val k) ∧ BinaryPrecision.Frame changed s.val t.val := by
  have width := data_width_all bank n v U hn (fun k hk => hw k (naturalIds_parts hk))
  have ready : Ready bank v s := ⟨fun k hk => by simpa only [hn k hk] using hs k (naturalIds_parts hk),
    fun k hk => hz k (by omega)⟩
  have slots : ∀k∈clearRegisters,k∈bank := fun k hk => (clearRegisters_mem k).mp hk |>.1
  obtain ⟨c0,u,e0,hc0,r0,good,width0,rawBank,rawWidth,four,f0⟩ :=
    resetNatural_executes bank naturalIds clearRegisters
      (fun k hk => by have := naturalIds_ge k hk;omega) slots n v U B hB hBU hw width hg
      (fun k hk hc => hv k (by
        by_contra hn
        exact hc ((clearRegisters_mem k).mpr ⟨hk,hn⟩))) input tape s hs ready (hz 4 (by decide))
  change Ready bank (clearedParts v) u at r0
  change Good bank (clearedParts v) at good
  change WidthBank bank B (clearedParts v) at width0
  change NatAssign.Bank naturalIds (resetNaturalBase n v) u.val at rawBank
  change ∀k∈naturalIds,(resetNaturalBase n v k).bits.length≤U at rawWidth
  have valid : ∀a∈clearPlan,a.Valid naturalIds := by
    intro a ha
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
    exact (clearNatural_mem k hk).1
  have literals : ∀a∈clearPlan,a.literalWidth≤U := by
    intro a ha
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp ha
    simp [NatAssign.Instruction.literalWidth]
  obtain ⟨c1,t,e1,hc1,b1,ready1,blank,frame1⟩ := naturalStage_parts bank naturalIds naturalIds_parts
    naturalIds_ge clearPlan valid (by decide) (resetNaturalBase n v) (clearedParts v) U rawWidth literals
    (clearedNaturals_agrees n v) input tape u rawBank r0.2 four
  have frame0 : BinaryPrecision.Frame changed s.val u.val := f0.mono (by
    intro k hk
    rcases Finset.mem_union.mp hk with hz|hp
    · exact Finset.mem_union_left _ (by simp only [Finset.mem_insert,Finset.mem_singleton] at hz ⊢;tauto)
    · exact Finset.mem_union_right _ (naturalIds_parts hp))
  refine ⟨c0+c1,t,e0.seq e1,?_,ready1,good,clearedParts_width v B hB hv,b1,
    clearedNaturals_width n v B hB hv hR,blank,frame0.trans frame1⟩
  have length : clearRegisters.length≤232 := by
    unfold clearRegisters
    exact (List.length_filter_le _ _).trans (by simp)
  have square : (U+2)^2≤(U+3)^2 := Nat.pow_le_pow_left (by omega) 2
  have nonzero : 1≤(U+3)^2 := by nlinarith
  unfold operationCost at hc0
  unfold stageCost at hc1
  nlinarith only [hc0,hc1,length,square,nonzero]

#print axioms reset_executes
end Maxwell.Continuum.Calibration.BasisForcing
