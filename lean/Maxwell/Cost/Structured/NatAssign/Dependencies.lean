import Maxwell.Cost.Structured.NatAssign.Values

/-! Exact input dependencies of fixed natural-word programs. Local arithmetic
bounds need only the operands actually read before being overwritten. -/
namespace Maxwell.Cost.Structured.NatAssign

def Instruction.sources : Instruction → Finset ℕ
  | .literal _ _ => ∅
  | .copy source _ => {source}
  | .add source target | .multiply source target => {source,target}

def dependencies : List Instruction → ℕ → Finset ℕ
  | [],i => {i}
  | a::rest,i => (dependencies rest i).biUnion fun j =>
      if j=a.target then a.sources else {j}

theorem Instruction.value_congr (a : Instruction) (v w : ℕ→ℕ)
    (h : ∀i∈a.sources,v i=w i) : a.value v=a.value w := by
  cases a with
  | literal target n => rfl
  | copy source target => exact h source (by simp [Instruction.sources])
  | add source target => exact congrArg₂ (fun x y : ℕ=>x+y) (h source (by simp [Instruction.sources])) (h target (by simp [Instruction.sources]))
  | multiply source target => exact congrArg₂ (fun x y : ℕ=>x*y) (h source (by simp [Instruction.sources])) (h target (by simp [Instruction.sources]))

theorem values_dependencies (xs : List Instruction) (v w : ℕ→ℕ) (i : ℕ)
    (h : ∀j∈dependencies xs i,v j=w j) : values xs v i=values xs w i := by
  induction xs generalizing v w with
  | nil => exact h i (by simp [dependencies])
  | cons a rest ih =>
    apply ih
    intro j hj
    by_cases ht : j=a.target
    · subst j
      simp only [Instruction.update,Function.update_self]
      apply a.value_congr
      intro q hq
      exact h q (by simp only [dependencies,Finset.mem_biUnion];exact ⟨a.target,hj,by simpa using hq⟩)
    · simp only [Instruction.update,Function.update_of_ne ht]
      exact h j (by simp only [dependencies,Finset.mem_biUnion];exact ⟨j,hj,by simp [ht]⟩)

theorem values_dependencies_width (ids sources : Finset ℕ) (xs : List Instruction)
    (hv : ∀a∈xs,a.Valid ids) (v : ℕ→ℕ) (B : ℕ)
    (hb : ∀i∈sources,(v i).bits.length ≤ B)
    (hc : ∀a∈xs,a.literalWidth ≤ B) (i : ℕ) (hi : i∈ids)
    (hd : dependencies xs i⊆sources) :
    (values xs v i).bits.length ≤ 2^xs.length*(B+1) := by
  let w : ℕ→ℕ := fun i=>if i∈sources then v i else 0
  have wb : ∀i∈ids,(w i).bits.length ≤ B := by
    intro j _
    by_cases hj : j∈sources
    · simpa [w,hj] using hb j hj
    · simp [w,hj]
  have he := values_dependencies xs v w i (fun j hj=>by simp [w,hd hj])
  rw [he]
  have hh := values_width ids xs hv w B wb hc i hi
  omega

/-- Only overwritten words can grow. Their bounds depend on the finite set of
actual source operands, even when unrelated retained words are much larger. -/
theorem values_local_width (ids sources : Finset ℕ) (xs : List Instruction)
    (hv : ∀a∈xs,a.Valid ids) (v : ℕ→ℕ) (W B : ℕ)
    (hw : ∀i∈ids,(v i).bits.length ≤ W)
    (hb : ∀i∈sources,(v i).bits.length ≤ B)
    (hc : ∀a∈xs,a.literalWidth ≤ B)
    (hd : ∀a∈xs,dependencies xs a.target⊆sources)
    (hg : 2^xs.length*(B+1) ≤ W) :
    ∀i∈ids,(values xs v i).bits.length ≤ W := by
  let w : ℕ→ℕ := fun i=>if i∈sources then v i else 0
  have wb : ∀i∈ids,(w i).bits.length ≤ B := by
    intro i _
    by_cases hi : i∈sources
    · simpa [w,hi] using hb i hi
    · simp [w,hi]
  intro i hi
  by_cases ht : ∃a∈xs,i=a.target
  · obtain ⟨a,ha,rfl⟩ := ht
    have he : values xs v a.target=values xs w a.target := values_dependencies xs v w a.target
      (fun j hj=>by simp [w,hd a ha hj])
    rw [he]
    have hh := values_width ids xs hv w B wb hc a.target hi
    omega
  · have he := values_preserves xs v i (by simpa only [not_exists,not_and] using ht)
    rw [he]
    exact hw i hi

#print axioms values_local_width
end Maxwell.Cost.Structured.NatAssign
