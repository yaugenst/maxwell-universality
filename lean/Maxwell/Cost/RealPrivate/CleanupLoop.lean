import Maxwell.Cost.RealPrivate.CleanupFrame

namespace Maxwell.Cost.RealPrivate.Cleanup
open RealSimulation.Control

def loop : Code := .loop 9 logLength body

def LogTail (origin index : ℕ) (entries : List ℕ) (s : RAMState) : Prop :=
  ∀ j (hj : j<entries.length), s.indices (slot origin 2 (index+j))=entries[j]

structure Clears (origin : ℕ) (entries : List ℕ) (s t : RAMState) : Prop where
  words : ∀ a, t.words (slot origin 0 a)=if a∈entries then 0 else s.words (slot origin 0 a)
  indices : ∀ a, t.indices (slot origin 0 a)=if a∈entries then 0 else s.indices (slot origin 0 a)

theorem loop_executes (input : RAMInput) (tape : ℕ→Bool) (origin index total : ℕ)
    (entries : List ℕ) (s : Store) (hc : Config origin total s.val)
    (hlen : total=index+entries.length) (hcursor : s.val.indices 9=index+1)
    (hlog : LogTail origin index entries s.val) :
    ∃ t, Executes input tape loop (37*entries.length+1) s t ∧
      Config origin total t.val ∧ t.val.indices 9=total+1 ∧
      Clears origin entries s.val t.val ∧ Frame origin s.val t.val := by
  induction entries generalizing index s with
  | nil =>
    refine ⟨s,?_,hc,by simp only [List.length_nil,Nat.add_zero] at hlen; omega,?_,Frame.refl _ _⟩
    · apply Executes.done
      rw [hcursor,hc.length,hlen]
      simp
    · constructor <;> intro a <;> simp
  | cons address rest ih =>
    have hread : s.val.indices (slot origin 2 index)=address := by
      have hh := hlog 0 (by simp)
      exact hh
    let mid := stepState s origin index address
    have run := step_executes input tape s origin index address hc.high hc.origin_word hc.zero hc.one
      hcursor hc.realZero hread
    have mc : Config origin total mid.val := step_config hc index address
    have mf : Frame origin s.val mid.val := step_frame s origin index address
    have ml : LogTail origin (index+1) rest mid.val := by
      intro j hj
      rw [mf.index_bank hc.high 2 (by decide) (by decide)]
      have hh := hlog (j+1) (by simp only [List.length_cons]; omega)
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    obtain ⟨t,et,tc,ti,tt,tf⟩ := ih (index+1) mid mc (by simp only [List.length_cons] at hlen; omega)
      (by simp [mid,Nat.add_assoc]) ml
    refine ⟨t,?_,tc,ti,?_,mf.trans tf⟩
    · have h := Executes.more (body := body) (by rw [hcursor,hc.length,hlen]; simp) run et
      convert h using 1 <;> first | rfl | simp only [List.length_cons]; omega
    · constructor
      · intro a
        rw [tt.words]
        change (if a∈rest then 0 else (stepState s origin index address).val.words (slot origin 0 a)) = _
        rw [step_words]
        by_cases he : a=address <;> by_cases hm : a∈rest <;> simp [he,hm]
      · intro a
        rw [tt.indices]
        change (if a∈rest then 0 else (stepState s origin index address).val.indices (slot origin 0 a)) = _
        rw [step_indices _ _ _ _ _ hc.high]
        by_cases he : a=address <;> by_cases hm : a∈rest <;> simp [he,hm]

end Maxwell.Cost.RealPrivate.Cleanup
