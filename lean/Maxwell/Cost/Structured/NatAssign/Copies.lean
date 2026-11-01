import Maxwell.Cost.Structured.NatAssign.Values

/-! A fixed family of disjoint word copies preserves its source bank and
loads the corresponding target words. No particular arithmetic encoding is
needed by the copying lemma. -/
namespace Maxwell.Cost.Structured.NatAssign

def copies (sources : List ℕ) (target : ℕ→ℕ) : List Instruction :=
  sources.map (fun i=>.copy i (target i))

theorem copies_source (sources : List ℕ) (target v : ℕ→ℕ) (i : ℕ)
    (outside : ∀j∈sources,target j≠i) : values (copies sources target) v i=v i := by
  apply values_preserves
  intro a ha
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp ha
  exact (outside j hj).symm

theorem copies_target (sources : List ℕ) (target : ℕ→ℕ)
    (separate : ∀i∈sources,∀j∈sources,target i≠j)
    (injective : ∀i∈sources,∀j∈sources,target i=target j→i=j)
    (v : ℕ→ℕ) (i : ℕ) (member : i∈sources) :
    values (copies sources target) v (target i)=v i := by
  induction sources generalizing v with
  | nil => simp at member
  | cons a rest ih =>
    change values (copies rest target) ((Instruction.copy a (target a)).update v) (target i)=v i
    by_cases tail : i∈rest
    · rw [ih (fun x hx y hy=>separate x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
        (fun x hx y hy=>injective x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) _ tail]
      exact Function.update_of_ne (separate a (by simp) i member).symm _ _
    · have eq : i=a := by simpa only [List.mem_cons,tail,or_false] using member
      subst i
      rw [values_preserves]
      · simp [Instruction.update,Instruction.target,Instruction.value]
      · intro instruction hi
        obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hi
        intro equality
        have same : a=j:=injective a (by simp) j (List.mem_cons_of_mem _ hj) equality
        exact tail (same ▸ hj)

theorem copies_valid (sources : List ℕ) (target : ℕ→ℕ) (ids : Finset ℕ)
    (source_mem : ∀i∈sources,i∈ids) (target_mem : ∀i∈sources,target i∈ids)
    (separate : ∀i∈sources,i≠target i) : ∀a∈copies sources target,a.Valid ids := by
  intro a ha
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp ha
  exact ⟨source_mem i hi,target_mem i hi,separate i hi⟩

theorem copies_executes (sources : List ℕ) (target : ℕ→ℕ) (ids : Finset ℕ)
    (source_mem : ∀i∈sources,i∈ids) (target_mem : ∀i∈sources,target i∈ids)
    (separate : ∀i∈sources,∀j∈sources,target i≠j)
    (injective : ∀i∈sources,∀j∈sources,target i=target j→i=j)
    (ge : ∀i∈ids,4≤ i) (v : ℕ→ℕ) (B : ℕ) (width : ∀i∈ids,(v i).bits.length≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (bank : Bank ids v s.val) (clear : Scratch s.val) :
    ∃steps t,Executes input tape (code (copies sources target)) steps s t ∧
      steps≤3000*8^sources.length*(B+2)^2 ∧
      Bank ids (values (copies sources target) v) t.val ∧
      (∀i∈sources,RationalAccumulator.Word t.val (target i) (v i)) ∧
      (∀i∈ids,(values (copies sources target) v i).bits.length≤ B) ∧ Scratch t.val ∧
      BinaryPrecision.Frame (changes (copies sources target)) s.val t.val := by
  have valid:=copies_valid sources target ids source_mem target_mem
    (fun i hi=>(separate i hi i hi).symm)
  obtain ⟨steps,t,execution,charge,output,scratch,frame⟩:=
    executes ids ge (copies sources target) valid v input tape s bank clear
  refine ⟨steps,t,execution,?_,output,?_,?_,scratch,frame⟩
  · apply charge.trans
    have cost:=price_bound ids (copies sources target) valid v B width (by
      intro a ha
      obtain ⟨i,_,rfl⟩:=List.mem_map.mp ha
      exact Nat.zero_le _)
    simpa only [copies,List.length_map] using cost
  · intro i hi
    simpa only [copies_target sources target separate injective v i hi] using output (target i) (target_mem i hi)
  · apply values_assignment_width ids (copies sources target) valid v B width
    intro a ha
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp ha
    trivial

#print axioms copies_target
#print axioms copies_executes
end Maxwell.Cost.Structured.NatAssign
