import Maxwell.Continuum.FourierTensorGeneratedTerm

/-! The actual Fourier input table stores three frequencies and two
amplitude numerators per alias. No wave coefficient is an input entry. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
open RationalDataflow.PartArray
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def aliasReadPlan : List (ℕ×ℕ) := [(0,20),(1,21),(2,22),(3,23),(4,24)]
def aliasLoaded {n : ℕ} (a : Table (5*n)) (r : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  rowPlanValues a 5 r aliasReadPlan v

theorem aliasLoaded_keep {n : ℕ} (a : Table (5*n)) (r : ℕ) (v : ℕ→Parts)
    (i : ℕ) (hi : i < 20 ∨ 24 < i) : aliasLoaded a r v i=v i := by
  simp (disch := omega) [aliasLoaded,aliasReadPlan,rowPlanValues]

theorem aliasLoaded_entry {n : ℕ} (a : Table (5*n)) (r : ℕ) (v : ℕ→Parts)
    (i : Fin 5) : aliasLoaded a r v (20+i.val)=a.getD (5*r+i.val) := by
  fin_cases i <;> simp [aliasLoaded,aliasReadPlan,rowPlanValues]

def FourierRows {n B : ℕ} (a : Table (5*n)) (q : Fin n→Fin 3→ℚ)
    (amp : Fin n→ComplexDyadic B) : Prop :=
  ∀r : Fin n,(∀i : Fin 3,(a.get ⟨5*r.val+i.val,by have := r.isLt;have := i.isLt;omega⟩).value=q r i ∧
      (a.get ⟨5*r.val+i.val,by have := r.isLt;have := i.isLt;omega⟩).Valid) ∧
    a.get ⟨5*r.val+3,by have := r.isLt;omega⟩=Parts.literal ((amp r).1.numerator:ℚ) ∧
    a.get ⟨5*r.val+4,by have := r.isLt;omega⟩=Parts.literal ((amp r).2.numerator:ℚ)

theorem FourierRows.loaded {n B : ℕ} {a : Table (5*n)} {q : Fin n→Fin 3→ℚ}
    {amp : Fin n→ComplexDyadic B} (h : FourierRows a q amp) (r : Fin n)
    (v : ℕ→Parts) (j : Fin 3→ℕ) (hj : ∀i,(v (17+i.val)).positive=j i) :
    AxisInputs (aliasLoaded a r.val v) (q r) j ∧
      aliasLoaded a r.val v 23=Parts.literal ((amp r).1.numerator:ℚ) ∧
      aliasLoaded a r.val v 24=Parts.literal ((amp r).2.numerator:ℚ) := by
  have hr := r.isLt
  refine ⟨?_,?_,?_⟩
  · intro i
    have hi := i.isLt
    rw [aliasLoaded_entry a r.val v ⟨i.val,by omega⟩,
      aliasLoaded_keep a r.val v (17+i.val) (by omega),
      Table.getD,dite_eq_left (by change 5*r.val+i.val<5*n;omega)]
    exact ⟨(h r).1 i |>.1,(h r).1 i |>.2,hj i⟩
  · have he := aliasLoaded_entry a r.val v 3
    change aliasLoaded a r.val v 23=a.getD (5*r.val+3) at he
    rw [Table.getD,dite_eq_left (by omega)] at he
    exact he.trans (h r).2.1
  · have he := aliasLoaded_entry a r.val v 4
    change aliasLoaded a r.val v 24=a.getD (5*r.val+4) at he
    rw [Table.getD,dite_eq_left (by omega)] at he
    exact he.trans (h r).2.2

theorem FactorReady.restored_row_frame {n D Q N : ℕ} {a : Table n} {b : Table (2*D)}
    {v w : ℕ→Parts} {s t : Store} (h : FactorReady a Q N b v s)
    (hr : Ready tensorBank w t) (ha : a.Ready t) (hb : b.OutputReady t)
    (hkeep : ∀i,10 ≤ i → i<1000 → i≠201 → i∉RowIndex.ids → t.val.tapes i=s.val.tapes i)
    (h4 : t.val.tapes 4=s.val.tapes 4) (hz : ∀i∈RowIndex.ids,Blank t.val i)
    (hc : Blank t.val 201) : FactorReady a Q N b w t := by
  refine ⟨hr,?_,⟨blank_of_eq h4 h.floor.1,?_⟩,?_,ha,hb,
    blank_of_eq (hkeep 144 (by decide) (by decide) (by decide) (by decide)) h.power,
    blank_of_eq (hkeep 146 (by decide) (by decide) (by decide) (by decide)) h.powerCount,
    blank_of_eq (hkeep 680 (by decide) (by decide) (by decide) (by decide)) h.inner,?_⟩
  · intro i hi
    have hip : i∈PhaseMachine.Runtime.ids := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
    have hd : ∀i∈PhaseMachine.Runtime.ids,10 ≤ i ∧ i<1000 ∧ i≠201 ∧ i∉RowIndex.ids := by decide
    have hh := hd i hip
    exact blank_of_eq (hkeep i hh.1 hh.2.1 hh.2.2.1 hh.2.2.2) (h.phase i hi)
  · intro i hi
    by_cases hid : i∈RowIndex.ids
    · exact hz i hid
    · have hh : 10 ≤ i ∧ i<1000 ∧ i≠201 := by
        simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
          Finset.mem_insert,Finset.mem_singleton] at hi
        omega
      exact blank_of_eq (hkeep i hh.1 hh.2.1 hh.2.2 hid) (h.floor.2 i hi)
  · intro i hi
    by_cases he : i=201
    · subst i
      simpa only [initialSetup,initialDimensions,show (201:ℕ)≠710 by decide,show (201:ℕ)≠711 by decide,
        ite_false,Word,Nat.zero_bits,BankArray.Word,BitTape.shifted_nil,Blank] using hc
    · have hd : ∀i∈setupIds,10 ≤ i ∧ i<1000 ∧ i∉RowIndex.ids := by decide
      have hh := hd i hi
      exact word_of_eq (hkeep i hh.1 hh.2.1 he hh.2.2) (h.setup i hi)
  · intro i hi
    have hh := savedPorts_range i hi
    exact blank_of_eq (hkeep i (by omega) (by omega) (by omega) (by
      simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton];omega)) (h.saved i hi)

#print axioms FourierRows.loaded
#print axioms FactorReady.restored_row_frame
end Maxwell.Continuum.Profile.WaveMachine.Runtime
