import Maxwell.Cost.Structured.NatAssign.Bounds

/-! Output widths for a fixed finite arithmetic stage. -/

namespace Maxwell.Cost.Structured.NatAssign

theorem values_width_bound (ids : Finset ℕ) (ins : List Instruction)
    (hv : ∀ a∈ins, a.Valid ids) (v : ℕ→ℕ) (B : ℕ)
    (hw : ∀ i∈ids, (v i).bits.length≤B)
    (hc : ∀ a∈ins, a.literalWidth≤B) :
    ∀ i∈ids, (values ins v i).bits.length+1≤2^ins.length*(B+1) := by
  induction ins generalizing v B with
  | nil => intro i hi; simpa only [values,List.length_nil,pow_zero,one_mul] using Nat.add_le_add_right (hw i hi) 1
  | cons a rest ih =>
    have ha : a.Valid ids := hv a (by simp)
    have hwa := instruction_width ids a ha v B hw (hc a (by simp))
    have hr := ih (fun b hb => hv b (by simp [hb])) (a.update v) (2*B+1) hwa
      (fun b hb => (hc b (by simp [hb])).trans (by omega))
    intro i hi
    calc
      _ ≤ 2^rest.length*(2*B+1+1) := hr i hi
      _ = _ := by simp only [List.length_cons,pow_succ]; ring

#print axioms values_width_bound

end Maxwell.Cost.Structured.NatAssign
