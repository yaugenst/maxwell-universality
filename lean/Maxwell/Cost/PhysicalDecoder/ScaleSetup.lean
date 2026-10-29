import Maxwell.Cost.Structured.NatAssign.Bounds

namespace Maxwell.Cost.PhysicalDecoder.ScaleSetup
open Structured RationalAccumulator

/-- Original source normalization beta precedes original matrix normalization
lambda. These are the retained input-derived words, not a new rescaling. -/
def source (i : Fin 4) : ℕ := ![506,507,504,505] i
def target (i : Fin 4) : ℕ := 354+i.val
def ids : Finset ℕ := {506,507,504,505,354,355,356,357}
def plan : List NatAssign.Instruction :=
  [.copy 506 354, .copy 507 355, .copy 504 356, .copy 505 357]
def initial (v : Fin 4 → ℕ) (j : ℕ) : ℕ :=
  if j=506 then v 0 else if j=507 then v 1 else if j=504 then v 2 else
    if j=505 then v 3 else 0
def changed : Finset ℕ := {0,1,2,3,354,355,356,357}
def code : Code := NatAssign.code plan

theorem plan_valid : ∀ a ∈ plan, a.Valid ids := by
  simp [plan, NatAssign.Instruction.Valid, ids]

theorem changes : NatAssign.changes plan = changed := by
  ext j
  simp [NatAssign.changes, plan, NatAssign.Instruction.target, changed]
  tauto

theorem executes (v : Fin 4 → ℕ) (B : ℕ) (hb : ∀ i, (v i).bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : ∀ i, Word s.val (source i) (v i)) (hz : ∀ i, Blank s.val (target i))
    (hr : NatAssign.Scratch s.val) :
    ∃ cost t, cost ≤ 3000*8^4*(B+2)^2 ∧ Executes input tape code cost s t ∧
      (∀ i, Word t.val (target i) (v i)) ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame changed s.val t.val := by
  have hbank : NatAssign.Bank ids (initial v) s.val := by
    intro j hj
    simp only [ids, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact hs 0
    · exact hs 1
    · exact hs 2
    · exact hs 3
    · exact (zero_word_iff_blank _ _).mpr (hz 0)
    · exact (zero_word_iff_blank _ _).mpr (hz 1)
    · exact (zero_word_iff_blank _ _).mpr (hz 2)
    · exact (zero_word_iff_blank _ _).mpr (hz 3)
  obtain ⟨cost, t, he, hc, ht, htr, hf⟩ := NatAssign.executes ids (by decide) plan
    plan_valid (initial v) input tape s hbank hr
  have hbits : ∀ j ∈ ids, (initial v j).bits.length ≤ B := by
    intro j _
    simp only [initial]
    split_ifs <;> first | exact hb _ | simp
  have hp := NatAssign.price_bound ids plan plan_valid (initial v) B hbits (by
    intro a ha
    simp only [plan, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl <;> simp [NatAssign.Instruction.literalWidth])
  refine ⟨cost, t, hc.trans (by simpa only [plan, List.length_cons, List.length_nil] using hp),
    he, ?_, htr, changes ▸ hf⟩
  intro i
  have h := ht (target i) (by fin_cases i <;> decide)
  fin_cases i <;> simpa [target, plan, NatAssign.values, NatAssign.Instruction.update,
    NatAssign.Instruction.value, NatAssign.Instruction.target, initial] using h

end Maxwell.Cost.PhysicalDecoder.ScaleSetup
