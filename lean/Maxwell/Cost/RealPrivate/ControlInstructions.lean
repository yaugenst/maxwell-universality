import Maxwell.Cost.RealPrivate.AccessSemantics

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

theorem jump_instruction (externalInput : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin : ℕ} {source : RAMState} {written : List ℕ}
    (s : Store) (h : Represents origin source written s.val) (pc : ℕ) :
    ∃ t, Executes externalInput tape (instruction L (.jump pc)) 2 s t ∧
      Represents origin {source with pc := pc} written t.val ∧
      CallerFrame origin s.val t.val :=
  ⟨_, literal_executes externalInput tape s sourcePC pc, h.put_pc pc,
    callerFrame_put s origin sourcePC pc (Or.inr (Or.inl (by decide)))⟩

theorem branch_real_instruction (externalInput : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin : ℕ} {source : RAMState} {written : List ℕ}
    (s : Store) (h : Represents origin source written s.val) (left right yes no : ℕ) :
    ∃ t, Executes externalInput tape (instruction L (.branchLE left right yes no)) 16 s t ∧
      Represents origin {source with pc := if source.words left ≤ source.words right then yes else no}
        written t.val ∧ CallerFrame origin s.val t.val := by
  have hl := getWord_correct externalInput tape s h left 0 (by decide)
  have hr := getWord_correct externalInput tape _ hl.2.1 right 1 (by decide)
  let s2 := worded (worded s left 0) right 1
  have hleft : s2.val.words 0 = source.words left := by
    simpa [s2, worded, Store.put, putWord] using hl.2.2.1
  have hright : s2.val.words 1 = source.words right := hr.2.2.1
  have he := realBranch_executes externalInput tape s2 yes no
  rw [hleft, hright] at he
  exact ⟨_, hl.1.seq (hr.1.seq he), hr.2.1.put_pc _,
    hl.2.2.2.trans (hr.2.2.2.trans
      (callerFrame_put s2 origin sourcePC _ (Or.inr (Or.inl (by decide)))))⟩

theorem branch_index_instruction (externalInput : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin : ℕ} {source : RAMState} {written : List ℕ}
    (s : Store) (h : Represents origin source written s.val) (left right yes no : ℕ) :
    ∃ t, Executes externalInput tape (instruction L (.branchIndexLE left right yes no)) 15 s t ∧
      Represents origin {source with pc := if source.indices left ≤ source.indices right then yes else no}
        written t.val ∧ CallerFrame origin s.val t.val := by
  have hl := getIndex_correct externalInput tape s h left leftRegister (by decide)
  have hr := getIndex_correct externalInput tape _ hl.2.1 right rightRegister (by decide)
  let s2 := indexed (indexed s left leftRegister) right rightRegister
  have hleft : s2.val.indices leftRegister = source.indices left := by
    simpa [s2, indexed, leftRegister, rightRegister, pointerRegister] using hl.2.2.1
  have hright : s2.val.indices rightRegister = source.indices right := hr.2.2.1
  let pc := if source.indices left ≤ source.indices right then yes else no
  have he : Executes externalInput tape
      (.branch leftRegister rightRegister (literal sourcePC yes) (literal sourcePC no)) 3 s2
      (s2.put sourcePC pc) := by
    by_cases hc : source.indices left ≤ source.indices right
    · have htest : s2.val.indices leftRegister ≤ s2.val.indices rightRegister := by
        rw [hleft, hright]; exact hc
      simpa [pc, hc] using Executes.yes (no := literal sourcePC no) htest
        (literal_executes externalInput tape s2 sourcePC yes)
    · have htest : ¬ s2.val.indices leftRegister ≤ s2.val.indices rightRegister := by
        rw [hleft, hright]; exact hc
      simpa [pc, hc] using Executes.no (yes := literal sourcePC yes) htest
        (literal_executes externalInput tape s2 sourcePC no)
  exact ⟨_, hl.1.seq (hr.1.seq he), hr.2.1.put_pc _,
    hl.2.2.2.trans (hr.2.2.2.trans
      (callerFrame_put s2 origin sourcePC _ (Or.inr (Or.inl (by decide)))))⟩

theorem Represents.drawn {origin : ℕ} {source : RAMState} {written : List ℕ}
    {s : Store} (h : Represents origin source written s.val) (dst : ℕ) (b : Bool)
    (hd : dst < origin) :
    Represents origin {source with randomCursor := source.randomCursor + 1} written (drawn s dst b).val := by
  have hw := h.word_scratch dst (if b then 1 else 0) hd
  refine ⟨hw.high, hw.origin_word, hw.zero, hw.one, hw.pc, hw.words, hw.indices,
    hw.real_output_length, hw.index_output_length, hw.real_output, hw.index_output,
    hw.log_length, hw.log_cells, ?_⟩
  exact congrArg (fun n => n + 1) h.random_cursor

end Maxwell.Cost.RealPrivate
