import Maxwell.Cost.DoublingInit.Common

namespace Maxwell.Cost.DoublingInit
open Structured
open RationalAccumulator (Blank)
open BankArray (Word)

def cleanupCode : Code := .seq (.call (TapeOps.clear 88))
  (.seq (.call (TapeOps.clear 89)) (.call (TapeOps.clear 37)))

theorem cleanup_executes (input : List Bool) (tape : ℕ → Bool) (xs ys index : List Bool)
    (s : Store) (h88 : Word s.val 88 xs) (h89 : Word s.val 89 ys) (h37 : Word s.val 37 index)
    (ss : BankArray.Scratch s.val) (h7 : Blank s.val 7)
    (rest : ∀ k, 90≤k → k≤92 → Blank s.val k) :
    ∃ t, Executes input tape cleanupCode (6*(xs.length+ys.length+index.length)+12) s t ∧
      Workspace t.val ∧ t.val.memory=s.val.memory ∧ Frame s.val t.val := by
  obtain ⟨xo,hx⟩ := h88
  obtain ⟨yo,hy⟩ := h89
  obtain ⟨io,hi⟩ := h37
  obtain ⟨a,ea,ta,fa⟩ := WordCall.clear 88 input tape xs xo s hx
  obtain ⟨b,eb,tb,fb⟩ := WordCall.clear 89 input tape ys yo a (by simpa [ta] using hy)
  obtain ⟨t,et,tt,ft⟩ := WordCall.clear 37 input tape index io b (by simpa [tb,ta] using hi)
  have global : t.val.tapes = Function.update (Function.update (Function.update s.val.tapes
      88 {BitTape.blank with head:=xo+xs.length}) 89 {BitTape.blank with head:=yo+ys.length})
      37 {BitTape.blank with head:=io+index.length} := by rw [tt,tb,ta]
  have keep (k : ℕ) (h88 : k≠88) (h89 : k≠89) (h37 : k≠37) : t.val.tapes k=s.val.tapes k := by
    simp [global,h88,h89,h37]
  refine ⟨t,?_,?_,ft.2.2.1.trans (fb.2.2.1.trans fa.2.2.1),
    (Frame.of_clear (by simp [Private,DoublingPass.Private]) fa).trans
      ((Frame.of_clear (by simp [Private,DoublingPass.Private]) fb).trans
        (Frame.of_clear (Or.inl rfl) ft))⟩
  · convert ea.seq (eb.seq et) using 1 <;> first | rfl | omega
  · rcases ss with ⟨s0,s1,s2,s3,s5,s6,s8,s9⟩
    refine ⟨⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_⟩,⟨io+index.length,by simp [global]⟩⟩
    all_goals first
    | exact RationalAccumulator.blank_of_eq (keep _ (by omega) (by omega) (by omega)) (by assumption)
    | skip
    intro k hk
    by_cases h88 : k=88
    · subst k; exact ⟨xo+xs.length,by simp [global]⟩
    by_cases h89 : k=89
    · subst k; exact ⟨yo+ys.length,by simp [global]⟩
    exact RationalAccumulator.blank_of_eq (keep k h88 h89 (by dsimp [DoublingPass.Private] at hk; omega))
      (rest k (by dsimp [DoublingPass.Private] at hk; omega) hk.2)

end Maxwell.Cost.DoublingInit
