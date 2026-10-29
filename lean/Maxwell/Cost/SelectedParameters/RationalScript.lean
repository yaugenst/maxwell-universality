import Maxwell.Cost.SelectedParameters.RationalScript.Sequence

namespace Maxwell.Cost.SelectedParameters.RationalScript
open Structured Rational

theorem clean_width (extra : Finset ℕ) (v : ℕ → ℕ) (B : ℕ)
    (hw : ∀ i ∈ ids extra, (v i).bits.length ≤ B) :
    ∀ i ∈ ids extra, (clean v i).bits.length ≤ B := by
  intro i hi
  by_cases hc : i∈common
  · simp [hc]
  · simpa [hc] using hw i hi

theorem clean_clean (v : ℕ → ℕ) : Clean (clean v) := by
  intro i hi
  simp [hi]

/-- A fixed rational script is executed by actual finite code. Choice
denominator positivity is the only value-dependent enable condition;
no final result, free arithmetic, or preinitialized common bank is supplied. -/
theorem executes (extra : Finset ℕ) (hextra : ∀ i ∈ extra, 540 ≤ i)
    (instructions : List Instruction) (hv : ∀ a ∈ instructions, a.Valid extra)
    (v : ℕ → ℕ) (B : ℕ) (hw : ∀ i ∈ ids extra, (v i).bits.length ≤ B)
    (he : Enabled instructions (clean v))
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hb : NatAssign.Bank (ids extra) v s.val) (hs : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape (code instructions) cost s t ∧
      cost ≤ coefficient instructions*(B+2)^2 ∧
      NatAssign.Bank (ids extra) (values instructions v) t.val ∧ NatAssign.Scratch t.val ∧
      (∀ i ∈ common, RationalAccumulator.Blank t.val i) ∧
      (∀ i ∈ ids extra, (values instructions v i).bits.length+2 ≤ widthFactor instructions*(B+2)) ∧
      BinaryPrecision.Frame (workspace instructions) s.val t.val := by
  have hc : ∀ a ∈ clear, a.Valid (ids extra) := by
    simp [clear,NatAssign.Instruction.Valid,ids,common]
  obtain ⟨ccost,u,ec,pc,bc,sc,fc⟩ := NatAssign.executes (ids extra) (ids_lower extra hextra)
    clear hc v input tape s hb hs
  have hcw := clean_width extra v B hw
  obtain ⟨rcost,t,er,pr,br,sr,fr⟩ := sequence_executes extra hextra instructions hv (clean v) B hcw he
    (clean_clean v) input tape u bc sc
  have hpc := NatAssign.price_bound (ids extra) clear hc v B hw (by simp [clear,NatAssign.Instruction.literalWidth])
  have hpc' : ccost ≤ 3000*8^7*(B+2)^2 := pc.trans hpc
  have hclean := fold_clean instructions (clean v) (clean_clean v)
  refine ⟨ccost+rcost,t,ec.seq er,?_,br,sr,?_,fold_width extra instructions hv (clean v) B hcw,?_⟩
  · calc
      ccost+rcost ≤ 3000*8^7*(B+2)^2+costFactor instructions*(B+2)^2 := Nat.add_le_add hpc' pr
      _ = coefficient instructions*(B+2)^2 := by simp only [coefficient,Nat.add_mul]
  · intro i hi
    have hb0 := br i (Finset.mem_union_right _ hi)
    rw [hclean i hi] at hb0
    exact (RationalAccumulator.zero_word_iff_blank t.val i).mp hb0
  · apply (fc.mono ?_).trans fr
    intro i hi
    simp [NatAssign.changes,clear,NatAssign.Instruction.target,workspace,common] at hi ⊢
    omega

theorem run (extra : Finset ℕ) (hextra : ∀ i ∈ extra, 540 ≤ i)
    (instructions : List Instruction) (hv : ∀ a ∈ instructions, a.Valid extra)
    (v : ℕ → ℕ) (B : ℕ) (hw : ∀ i ∈ ids extra, (v i).bits.length ≤ B)
    (he : Enabled instructions (clean v))
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hb : NatAssign.Bank (ids extra) v s.val) (hs : NatAssign.Scratch s.val) :
    ∃ t : Store, (runPriced ((program instructions).next input tape)
        (coefficient instructions*(B+2)^2+1) s.val).finished = some (t.place (code instructions).size) ∧
      (runPriced ((program instructions).next input tape)
        (coefficient instructions*(B+2)^2+1) s.val).instructions ≤ coefficient instructions*(B+2)^2 ∧
      NatAssign.Bank (ids extra) (values instructions v) t.val ∧ NatAssign.Scratch t.val ∧
      (∀ i ∈ common, RationalAccumulator.Blank t.val i) ∧
      (∀ i ∈ ids extra, (values instructions v i).bits.length+2 ≤ widthFactor instructions*(B+2)) ∧
      BinaryPrecision.Frame (workspace instructions) s.val t.val := by
  obtain ⟨cost,t,et,hcost,ht,hst,hcommon,hwidth,hf⟩ := executes extra hextra instructions hv v B hw he input tape s hb hs
  have hr := et.compiled_run (coefficient instructions*(B+2)^2+1) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hcost,ht,hst,hcommon,hwidth,hf⟩

end Maxwell.Cost.SelectedParameters.RationalScript
