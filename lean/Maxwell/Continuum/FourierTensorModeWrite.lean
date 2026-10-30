import Maxwell.Continuum.FourierTensorModePrepare
import Maxwell.Continuum.RationalDataflowRowWriteValues

/-! The five prepared values are written at actual row addresses. The
descending order matches the runtime countdown's filled-table invariant. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrepare
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def writePlan : List (ℕ×ℕ) := [(4,10),(3,9),(2,6),(1,5),(0,4)]
def writeCode : Code := rowWritePlanCode 5 writePlan
def written (P R : ℕ) (a : Table (2*aliasArraySize R)) (b : Table (5*RowArithmetic.rowCount R))
    (j : Fin 3) (r : Fin (RowArithmetic.rowCount R)) (v : ℕ→Parts) : Table (5*RowArithmetic.rowCount R) :=
  rowWriteTable 5 r.val writePlan (values P R a j r v) b

theorem write_floor_frame {input : List Bool} {tape : ℕ→Bool} {cost : ℕ} {s t : Store}
    (e : Executes input tape writeCode cost s t) (h : DyadicFloor.Clean s.val)
    (f : RowWriteFrame s.val t.val) (hz : ∀i∈RowIndex.ids,Blank t.val i) : DyadicFloor.Clean t.val := by
  refine ⟨RationalAccumulator.blank_of_eq (e.protectsTape 4 (by decide)) h.1,?_⟩
  intro i hi
  by_cases hr : i∈RowIndex.ids
  · exact hz i hr
  · have hh : 10 ≤ i ∧ i≠37 := by
      simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    exact RationalAccumulator.blank_of_eq (f.tapes i hh.1 hh.2 hr) (h.2 i hi)

theorem write_natural_frame {n : ℕ→ℕ} {s t : Store}
    (h : NatAssign.Bank ModeIndex.ports n s.val) (f : RowWriteFrame s.val t.val) :
    NatAssign.Bank ModeIndex.ports n t.val := by
  intro i hi
  have hr : 310 ≤ i ∧ i≤322 := Finset.mem_Icc.mp hi
  exact RationalAccumulator.word_of_eq (f.tapes i (by omega) (by omega)
    (by simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton];omega)) (h i hi)

theorem write_executes (P R W : ℕ) (a : Table (2*aliasArraySize R))
    (b : Table (5*RowArithmetic.rowCount R)) (j : Fin 3) (r : Fin (RowArithmetic.rowCount R))
    (v : ℕ→Parts) (hm : b.MetadataWidth W)
    (hfit : ∀x∈writePlan,(values P R a j r v x.2).Width (addressValue b.width))
    (hpos : 0<addressValue b.width) (hsep : b.Separated) (hdisj : a.SeparatedFrom b)
    (input : List Bool) (tape : ℕ→Bool) (word : List Bool) (hlen : word.length≤W)
    (hrow : addressValue word=r.val) (s : Store)
    (hr : RationalDataflow.Ready RowArithmetic.bank (values P R a j r v) s)
    (ha : a.Ready s) (hb : b.OutputReady s) (hc : BankArray.Word s.val 201 word)
    (hn : NatAssign.Bank ModeIndex.ports
      (ModeDecode.after (ModeIndex.readValues R a j r v) (ModeIndex.values j R (aliasArraySize R) r.val)) s.val)
    (hz : DyadicFloor.Clean s.val) (hp : Word s.val 144 (2^P)) :
    ∃cost t,Executes input tape writeCode cost s t ∧ cost≤2^35*(W+11)^2 ∧
      RationalDataflow.Ready RowArithmetic.bank (values P R a j r v) t ∧ a.Ready t ∧
      (written P R a b j r v).OutputReady t ∧
      NatAssign.Bank ModeIndex.ports
        (ModeDecode.after (ModeIndex.readValues R a j r v) (ModeIndex.values j R (aliasArraySize R) r.val)) t.val ∧
      DyadicFloor.Clean t.val ∧ Word t.val 144 (2^P) ∧ BankArray.Word t.val 201 word ∧
      t.val.tapes 201=s.val.tapes 201 ∧ t.val.output=s.val.output := by
  have hblank : ∀i∈RowIndex.ids,Blank s.val i := by
    intro i hi
    exact hz.2 i (Finset.mem_union_right _ (by
      simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
      simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton]
      tauto))
  have hix : ∀x∈writePlan,5*addressValue word+x.1<5*RowArithmetic.rowCount R := by
    intro x hx
    have hh : x.1<5 := by simp only [writePlan,List.mem_cons,List.not_mem_nil,or_false] at hx;rcases hx with rfl|rfl|rfl|rfl|rfl <;> decide
    rw [hrow]
    have := r.isLt
    omega
  obtain ⟨cost,t,e,hcost,rt,at',bt,zt,ft⟩ := rowWritePlan_executes a b RowArithmetic.bank 5 3 W writePlan
    (by decide) (by decide) hm (values P R a j r v) hfit hpos hsep hdisj input tape word hlen hix
    s hr ha hb hc hblank
  rw [hrow] at bt
  refine ⟨cost,t,e,?_,rt,at',bt,write_natural_frame hn ft,write_floor_frame e hz ft zt,
    RationalAccumulator.word_of_eq (ft.tapes 144 (by decide) (by decide) (by decide)) hp,
    BankArray.word_of_eq ft.counter hc,ft.counter,ft.output⟩
  have hh : rowPlanCost 5 3 W writePlan=5*(2^30*(W+11)^2)+1 := by rfl
  rw [hh] at hcost
  nlinarith only [hcost,Nat.zero_le W]

#print axioms write_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrepare
