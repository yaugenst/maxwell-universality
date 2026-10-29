import Maxwell.Cost.SelectedParameters.RationalScript.Syntax

namespace Maxwell.Cost.SelectedParameters.RationalScript
open Structured Rational

theorem ids_lower (extra : Finset ℕ) (h : ∀ i ∈ extra, 540 ≤ i) :
    ∀ i ∈ ids extra, 4 ≤ i := by
  intro i hi
  simp only [ids,common,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with he | hc
  · exact (by omega : 4 ≤ 540).trans (h i he)
  · omega

theorem literal_executes (extra : Finset ℕ) (hextra : ∀ i ∈ extra, 540 ≤ i)
    (num den n d : ℕ) (hnum : num ∈ extra) (hden : den ∈ extra)
    (v : ℕ → ℕ) (B : ℕ) (hw : ∀ i ∈ ids extra, (v i).bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hb : NatAssign.Bank (ids extra) v s.val) (hs : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape (NatAssign.code (literalInstructions num den n d)) cost s t ∧
      cost ≤ 3000*8^9*(n.bits.length+d.bits.length+1)^2*(B+2)^2 ∧
      NatAssign.Bank (ids extra) (after v num den (n,d)) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame (Rational.workspace num den) s.val t.val := by
  have hv : ∀ a ∈ literalInstructions num den n d, a.Valid (ids extra) := by
    simp [literalInstructions,clear,NatAssign.Instruction.Valid,ids,common,hnum,hden]
  obtain ⟨cost,t,et,hcost,ht,hst,hf⟩ := NatAssign.executes (ids extra) (ids_lower extra hextra)
    (literalInstructions num den n d) hv v input tape s hb hs
  have heq : NatAssign.values (literalInstructions num den n d) v=after v num den (n,d) := rfl
  refine ⟨cost,t,et,?_,heq ▸ ht,hst,hf.mono ?_⟩
  · have hp := NatAssign.price_bound (ids extra) (literalInstructions num den n d) hv v
      (B+n.bits.length+d.bits.length) (fun i hi => (hw i hi).trans (by omega)) (by
        intro a ha
        simp only [literalInstructions,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with (rfl | rfl) | ha
        · simp only [NatAssign.Instruction.literalWidth]; omega
        · simp only [NatAssign.Instruction.literalWidth]; omega
        · simp only [clear,List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [NatAssign.Instruction.literalWidth])
    change _ ≤ 3000*8^9*(B+n.bits.length+d.bits.length+2)^2 at hp
    have harg : B+n.bits.length+d.bits.length+2 ≤ (n.bits.length+d.bits.length+1)*(B+2) := by nlinarith
    calc
      cost  ≤  3000*8^9*(B+n.bits.length+d.bits.length+2)^2 := hcost.trans hp
      _  ≤  3000*8^9*((n.bits.length+d.bits.length+1)*(B+2))^2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 2)
      _ = _ := by ring
  · intro i hi
    simp [NatAssign.changes,literalInstructions,clear,NatAssign.Instruction.target,
      Rational.workspace,common] at hi ⊢
    omega

end Maxwell.Cost.SelectedParameters.RationalScript
