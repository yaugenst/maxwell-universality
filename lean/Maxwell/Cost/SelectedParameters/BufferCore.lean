import Maxwell.Cost.SelectedParameters.BufferValues
import Maxwell.Cost.SelectedParameters.LeastLoop
import Maxwell.Cost.RationalCompare

namespace Maxwell.Cost.SelectedParameters.Buffer
open Structured RationalAccumulator
set_option maxHeartbeats 1500000

def searchCode : Code := LeastLoop.code 35 RationalCompare.code (NatAssign.code advance)
def testCost (B : ℕ) : ℕ := 8000*(B+2)^2
def advanceCost (B : ℕ) : ℕ := 3000*8^31*(B+2)^2
def initializationCost (B : ℕ) : ℕ := 3000*8^32*(B+3)^2

structure Ready (d : Data) (n : ℕ) (s : Store) : Prop where
  bank : NatAssign.Bank ids (values d n) s.val
  scratch : NatAssign.Scratch s.val

theorem test (d : Data) (n N B : ℕ) (hn : n ≤ N) (hd : d.Bounded B)
    (input : List Bool) (randomTape : ℕ → Bool) (s : Store) (hs : Ready d n s) :
    ∃ cost t, Executes input randomTape RationalCompare.code cost s t ∧
      cost ≤ testCost (width N B) ∧ Ready d n t ∧
      t.val.registers 35 = decide (¬Test d n) ∧ BinaryPrecision.Frame workspace s.val t.val := by
  have hbank : RationalAccumulator.Bank s.val (values d n) := by
    intro i hi hj
    exact hs.bank i (by simp only [ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]; omega)
  have scratch : RationalAccumulator.Scratch s.val 0 :=
    ⟨hs.scratch 0 (by decide),(zero_word_iff_blank _ _).mpr (hs.scratch 1 (by decide)),
      hs.scratch 2 (by decide),hs.scratch 3 (by decide)⟩
  have hbits : ∀ i, 30 ≤ i → i ≤ 33 → (values d n i).bits.length ≤ width N B :=
    fun i _ _ => values_width d n N B hn hd i
  obtain ⟨cost,t,hcost,he,ht,bt,st,ft⟩ := RationalCompare.compare input randomTape
    (values d n) (width N B) hbits (by simp [values]) (by simp [values])
    (by simp [values]) (by simp [values]) s hbank scratch
  refine ⟨cost,t,he,hcost,⟨?_,?_⟩,?_,?_⟩
  · intro i hi
    by_cases hr : 30 ≤ i ∧ i ≤ 36
    · exact bt i hr.1 hr.2
    · exact word_of_eq (ft.2.2.2.2.2.1 i (ids_ge i hi) (by omega)) (hs.bank i hi)
  · intro i hi
    interval_cases i
    · exact st.1
    · exact (zero_word_iff_blank _ _).mp st.2.1
    · exact st.2.2.1
    · exact st.2.2.2
  · simpa [values,Test,not_le] using ht
  · refine ⟨ft.1,ft.2.1,ft.2.2.1,ft.2.2.2.1,ft.2.2.2.2.1,?_⟩
    intro i hi
    simp only [workspace,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
    exact ft.2.2.2.2.2.1 i (by omega) (by omega)

theorem next (d : Data) (n N B : ℕ) (hn : n ≤ N) (hd : d.Bounded B)
    (input : List Bool) (randomTape : ℕ → Bool) (s : Store) (hs : Ready d n s) :
    ∃ cost t, Executes input randomTape (NatAssign.code advance) cost s t ∧
      cost ≤ advanceCost (width N B) ∧ Ready d (n+1) t ∧ BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost,t,he,hcost,bt,st,ft⟩ := NatAssign.executes ids ids_ge advance advance_valid
    (values d n) input randomTape s hs.bank hs.scratch
  have hprice := NatAssign.price_bound ids advance advance_valid (values d n)
    (width N B) (fun i _ => values_width d n N B hn hd i) (by
      simp [advance,advancePrefix,recompute,NatAssign.Instruction.literalWidth,width_one])
  rw [show advance.length=31 by rfl] at hprice
  refine ⟨cost,t,he,hcost.trans hprice,⟨?_,st⟩,ft.mono (by decide)⟩
  intro i hi
  rw [← advance_values d n i hi]
  exact bt i hi

theorem initialize_executes (v : ℕ → ℕ) (B : ℕ) (hwidth : ∀ i ∈ ids, (v i).bits.length ≤ B)
    (input : List Bool) (randomTape : ℕ → Bool) (s : Store)
    (hbank : NatAssign.Bank ids v s.val) (hscratch : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input randomTape (NatAssign.code initialization) cost s t ∧
      cost ≤ initializationCost B ∧ Ready (initialData v) 0 t ∧ BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost,t,he,hcost,bt,st,ft⟩ := NatAssign.executes ids ids_ge initialization initialization_valid
    v input randomTape s hbank hscratch
  have hprice := NatAssign.price_bound ids initialization initialization_valid v (B+1)
    (fun i hi => (hwidth i hi).trans (by omega)) (by
      simp [initialization,initializePrefix,recompute,NatAssign.Instruction.literalWidth])
  rw [show initialization.length=32 by rfl] at hprice
  refine ⟨cost,t,he,by simpa only [initializationCost,Nat.add_assoc] using hcost.trans hprice,
    ⟨?_,st⟩,ft.mono (by decide)⟩
  intro i hi
  rw [← initialization_values v i hi]
  exact bt i hi

def searchCost (N B : ℕ) : ℕ :=
  testCost (width N B)+1+N*(advanceCost (width N B)+testCost (width N B)+1)

theorem search (d : Data) (B : ℕ) (hd : d.Bounded B) (hexists : ∃ n, Test d n)
    (input : List Bool) (randomTape : ℕ → Bool) (s : Store) (hs : Ready d 0 s) :
    ∃ cost t, Executes input randomTape searchCode cost s t ∧ cost ≤ searchCost (Nat.find hexists) B ∧
      Ready d (Nat.find hexists) t ∧ BinaryPrecision.Frame workspace s.val t.val := by
  let N := Nat.find hexists
  let R : ℕ → Store → Prop := fun n t => Ready d n t ∧ BinaryPrecision.Frame workspace s.val t.val
  have htest : ∀ n, n ≤ N → ∀ t, R n t →
      ∃ cost u, Executes input randomTape RationalCompare.code cost t u ∧
        cost ≤ testCost (width N B) ∧ R n u ∧ u.val.registers 35=decide (¬Test d n) := by
    intro n hn t htr
    obtain ⟨cost,u,he,hcost,hu,ht,hf⟩ := test d n N B hn hd input randomTape t htr.1
    exact ⟨cost,u,he,hcost,⟨hu,htr.2.trans hf⟩,ht⟩
  have hadvance : ∀ n, n < N → ∀ t, R n t →
      ∃ cost u, Executes input randomTape (NatAssign.code advance) cost t u ∧
        cost ≤ advanceCost (width N B) ∧ R (n+1) u := by
    intro n hn t htr
    obtain ⟨cost,u,he,hcost,hu,hf⟩ := next d n N B (by omega) hd input randomTape t htr.1
    exact ⟨cost,u,he,hcost,hu,htr.2.trans hf⟩
  obtain ⟨cost,t,he,hcost,ht⟩ := LeastLoop.executes (Test d) hexists 35 RationalCompare.code
    (NatAssign.code advance) (testCost (width N B)) (advanceCost (width N B))
    input randomTape R htest hadvance s ⟨hs,BinaryPrecision.Frame.refl _ _⟩
  exact ⟨cost,t,he,hcost,ht⟩

def code : Code := .seq (NatAssign.code initialization) searchCode

theorem initialData_bounded (v : ℕ → ℕ) (B : ℕ) (hw : ∀ i ∈ ids, (v i).bits.length ≤ B) :
    (initialData v).Bounded B := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals apply hw; simp [ids,base]

theorem executes (v : ℕ → ℕ) (B : ℕ) (hwidth : ∀ i ∈ ids, (v i).bits.length ≤ B)
    (hexists : ∃ n, Test (initialData v) n)
    (input : List Bool) (randomTape : ℕ → Bool) (s : Store)
    (hbank : NatAssign.Bank ids v s.val) (hscratch : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input randomTape code cost s t ∧
      cost ≤ initializationCost B+searchCost (Nat.find hexists) B ∧
      Ready (initialData v) (Nat.find hexists) t ∧ BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c1,u,e1,p1,h1,f1⟩ := initialize_executes v B hwidth input randomTape s hbank hscratch
  obtain ⟨c2,t,e2,p2,h2,f2⟩ := search (initialData v) B (initialData_bounded v B hwidth) hexists
    input randomTape u h1
  exact ⟨c1+c2,t,e1.seq e2,Nat.add_le_add p1 p2,h2,f1.trans f2⟩

end Maxwell.Cost.SelectedParameters.Buffer
