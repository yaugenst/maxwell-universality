import Maxwell.Cost.SelectedParameters.RationalScript.Instruction

namespace Maxwell.Cost.SelectedParameters.RationalScript
open Structured Rational

theorem workspace_cons (a : Instruction) (rest : List Instruction) :
    workspace (a::rest) = Rational.workspace a.numerator a.denominator ∪ workspace rest := by
  ext i
  simp [workspace,outputs,Rational.workspace,or_comm,or_left_comm]

theorem fold_clean (instructions : List Instruction) (v : ℕ → ℕ) (hc : Clean v) :
    Clean (fold instructions v) := by
  induction instructions generalizing v with
  | nil => exact hc
  | cons a rest ih => exact ih (a.update v) (a.update_clean v)

theorem fold_width (extra : Finset ℕ) (instructions : List Instruction)
    (hv : ∀ a ∈ instructions, a.Valid extra) (v : ℕ → ℕ) (B : ℕ)
    (hw : ∀ i ∈ ids extra, (v i).bits.length ≤ B) :
    ∀ i ∈ ids extra, (fold instructions v i).bits.length+2 ≤ widthFactor instructions*(B+2) := by
  induction instructions generalizing v B with
  | nil => intro i hi; simpa only [fold,widthFactor,one_mul] using Nat.add_le_add_right (hw i hi) 2
  | cons a rest ih =>
    have ha := a.width extra (hv a (by simp)) v B hw
    have ht := ih (fun a ha => hv a (by simp [ha])) (a.update v) (a.nextWidth B) ha
    intro i hi
    calc
      (fold (a::rest) v i).bits.length+2 ≤ widthFactor rest*(a.nextWidth B+2) := ht i hi
      _ ≤ widthFactor rest*(a.growth*(B+2)) := Nat.mul_le_mul_left _ (a.nextWidth_growth B)
      _ = widthFactor (a::rest)*(B+2) := by simp only [widthFactor,Nat.mul_assoc]

theorem sequence_executes (extra : Finset ℕ) (hextra : ∀ i ∈ extra, 540 ≤ i)
    (instructions : List Instruction) (hv : ∀ a ∈ instructions, a.Valid extra)
    (v : ℕ → ℕ) (B : ℕ) (hw : ∀ i ∈ ids extra, (v i).bits.length ≤ B)
    (he : Enabled instructions v) (hc : Clean v)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hb : NatAssign.Bank (ids extra) v s.val) (hs : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape (sequence instructions) cost s t ∧
      cost ≤ costFactor instructions*(B+2)^2 ∧
      NatAssign.Bank (ids extra) (fold instructions v) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame (workspace instructions) s.val t.val := by
  induction instructions generalizing v B s with
  | nil =>
    have hq : 1 ≤ (B+2)^2 := Nat.one_le_pow _ _ (by omega)
    exact ⟨1,s,.skip s,by simpa only [costFactor,one_mul] using hq,hb,hs,BinaryPrecision.Frame.refl _ _⟩
  | cons a rest ih =>
    obtain ⟨acost,u,ea,pa,ba,sa,fa⟩ := instruction_executes extra hextra a (hv a (by simp)) v B hw
      he.1 hc input tape s hb hs
    have ha := a.width extra (hv a (by simp)) v B hw
    obtain ⟨rcost,t,er,pr,br,sr,fr⟩ := ih (fun a ha => hv a (by simp [ha])) (a.update v)
      (a.nextWidth B) ha he.2 (a.update_clean v) u ba sa
    refine ⟨acost+rcost,t,ea.seq er,?_,br,sr,?_⟩
    · have ht := Nat.mul_le_mul_left (costFactor rest) (Nat.pow_le_pow_left (a.nextWidth_growth B) 2)
      calc
        acost+rcost ≤ a.coefficient*(B+2)^2+costFactor rest*(a.nextWidth B+2)^2 := Nat.add_le_add pa pr
        _ ≤ a.coefficient*(B+2)^2+costFactor rest*(a.growth*(B+2))^2 := Nat.add_le_add_left ht _
        _ = costFactor (a::rest)*(B+2)^2 := by simp only [costFactor]; ring
    · rw [workspace_cons]
      exact (fa.mono Finset.subset_union_left).trans (fr.mono Finset.subset_union_right)

end Maxwell.Cost.SelectedParameters.RationalScript
