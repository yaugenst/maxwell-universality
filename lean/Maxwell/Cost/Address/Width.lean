import Maxwell.Cost.Address
import Maxwell.Cost.VisitedExecution

namespace Maxwell.Cost.Address
open HornerMultiply (PrefixTape)

def Within (width : ℕ) (s : BitRAMState) : Prop := s.address.length≤width

instance (W : ℕ) : DecidablePred (Within W) := fun s => inferInstanceAs (Decidable (s.address.length≤W))

set_option maxRecDepth 8192 in
theorem advance_visited (workTape : ℕ) (input : List Bool) (randomTape : ℕ→Bool)
    (s : BitRAMState) (b : Bool) (W : ℕ) (hpc : s.pc=1)
    (hread : (s.tapes workTape).cells ((s.tapes workTape).head-1)=some b)
    (hwidth : s.address.length+1≤W) :
    VisitedPriced ((load workTape).next input randomTape) (Within W) 6 s (advance workTape s b) := by
  have hstart : s.address.length≤W := by omega
  apply checkedInstructions_sound _ (Within W) (instructions := 5)
  simp [checkedInstructions,Within,load,BitRAM.next,hpc,hread,BitTape.read,
    advance,BitRAMState.setTape,BitRAMState.setRegister,hstart,hwidth]

set_option maxRecDepth 8192 in
theorem stop_visited (workTape : ℕ) (input : List Bool) (randomTape : ℕ→Bool)
    (s : BitRAMState) (W : ℕ) (hpc : s.pc=1)
    (hread : (s.tapes workTape).cells ((s.tapes workTape).head-1)=none)
    (hwidth : s.address.length≤W) :
    VisitedPriced ((load workTape).next input randomTape) (Within W) 4 s (stop workTape s) := by
  apply checkedInstructions_sound _ (Within W) (instructions := 3)
  simp [checkedInstructions,Within,load,BitRAM.next,hpc,hread,BitTape.read,
    stop,BitRAMState.setTape,BitRAMState.setRegister,hwidth]

/-- Every intermediate address has at most the initial length plus the
number of source symbols. Each push and each charged read is retained. -/
theorem loop_visited (workTape : ℕ) (input : List Bool) (randomTape : ℕ→Bool)
    (bits : List Bool) (origin : ℤ) (W : ℕ) (s : BitRAMState) (hpc : s.pc=1)
    (hword : PrefixTape (s.tapes workTape) bits origin) (hwidth : bits.length+s.address.length≤W) :
    ∃ t, VisitedPriced ((load workTape).next input randomTape) (Within W)
        (6*bits.length+4) s t ∧ t.pc=6 ∧ t.address=bits++s.address := by
  induction bits using List.reverseRecOn generalizing s with
  | nil =>
    refine ⟨stop workTape s,?_,rfl,rfl⟩
    simpa using stop_visited workTape input randomTape s W hpc hword.nil_read (by simpa using hwidth)
  | append_singleton bits b ih =>
    have hb : s.address.length+1≤W := by simp only [List.length_append,List.length_singleton] at hwidth; omega
    have hs := advance_visited workTape input randomTape s b W hpc hword.last_read hb
    obtain ⟨t,ht,hp,ha⟩ := ih (advance workTape s b) rfl
      (advance_prefix workTape s bits origin b hword) (by simpa [advance,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hwidth)
    refine ⟨t,?_,hp,?_⟩
    · convert hs.trans ht using 1
      simp
      omega
    · simpa [advance,List.append_assoc] using ha

/-- The full load has a uniform bound at every actual instruction boundary,
including its initial state before addressClear executes. -/
theorem load_visited (workTape : ℕ) (input : List Bool) (randomTape : ℕ→Bool)
    (bits : List Bool) (origin : ℤ) (s : BitRAMState) (hpc : s.pc=0)
    (hword : s.tapes workTape=BitTape.shiftedEnd bits origin) :
    ∃ t, VisitedPriced ((load workTape).next input randomTape)
        (Within (max s.address.length bits.length)) (6*bits.length+5) s t ∧
      t.pc=6 ∧ t.address=bits := by
  let start := {s with pc:=1,address:=[]}
  have hs : VisitedPriced ((load workTape).next input randomTape)
      (Within (max s.address.length bits.length)) 1 s start := by
    apply VisitedPriced.step (extra := 0) (rest := .refl (by simp [Within,start]))
    · exact le_max_left _ _
    · simp [BitRAM.next,load,hpc,start]
  obtain ⟨t,ht,hp,ha⟩ := loop_visited workTape input randomTape bits origin
    (max s.address.length bits.length) start rfl
    (by simpa [start,hword] using PrefixTape.shiftedEnd bits origin)
    (by simp [start])
  refine ⟨t,?_,hp,?_⟩
  · convert hs.trans ht using 1
    omega
  · simpa [start] using ha

/-- Direct prefix form required by the bit-to-real simulator. -/
theorem load_prefix (workTape : ℕ) (input : List Bool) (randomTape : ℕ→Bool)
    (bits : List Bool) (origin : ℤ) (s : BitRAMState) (hpc : s.pc=0)
    (hword : s.tapes workTape=BitTape.shiftedEnd bits origin)
    (n : ℕ) (u : BitRAMState) (hn : n≤6*bits.length+5)
    (hu : PricedSteps ((load workTape).next input randomTape) n s u) :
    u.address.length≤max s.address.length bits.length := by
  obtain ⟨t,ht,_,_⟩ := load_visited workTape input randomTape bits origin s hpc hword
  exact ht.prefix_bound hn hu

end Maxwell.Cost.Address
