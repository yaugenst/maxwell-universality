import Maxwell.Continuum.RationalDataflowMatrixInverseData

/-! A fixed traversal writes every inverse entry into its own rational
register. The original matrix inputs survive the entire traversal. -/
namespace Maxwell.Continuum.RationalDataflow.MatrixInverse
open PolynomialExpression
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def storeEntry (n : ℕ) (i j : Fin n) : Control :=
  (entryControl n i j).andThen
    (.step (.literal (output n i j) 0) (.step (.binary .add (output n i j) (output n i j) (base n)) .done))
def traversal (n : ℕ) : List (Fin n×Fin n) → Control
  | [] => .done
  | (i,j)::rest => (storeEntry n i j).andThen (traversal n rest)
def coordinates (n : ℕ) : List (Fin n×Fin n) := List.ofFn (fun i => (index n).symm i)
def control (n : ℕ) : Control := traversal n (coordinates n)
def registers (n : ℕ) : Finset ℕ := Finset.range (base n+2*determinantNodes n 1+3)
def entrySteps (n : ℕ) : ℕ := 6*determinantNodes n 1+8
def steps (n : ℕ) : ℕ := n*n*entrySteps n

theorem coordinates_complete (n : ℕ) (i j : Fin n) : (i,j)∈coordinates n := by
  apply List.mem_ofFn.mpr
  exact ⟨index n (i,j),(index n).symm_apply_apply (i,j)⟩

theorem output_injective (n : ℕ) : Function.Injective (fun p : Fin n×Fin n => output n p.1 p.2) := by
  intro a b h
  apply (index n).injective
  apply Fin.ext
  change n*n+(index n a).val=n*n+(index n b).val at h
  omega

theorem entry_subset (n : ℕ) (i j : Fin n) :
    QuotientExpression.registers (numerator n i j) (denominator n) (base n)⊆registers n := by
  have hp := numerator_nodes n i j
  have hq := denominator_nodes n
  apply Finset.range_mono
  change base n+(numerator n i j).nodes+(denominator n).nodes+3≤base n+2*determinantNodes n 1+3
  omega

theorem store_valid (n : ℕ) (i j : Fin n) : (storeEntry n i j).Valid (registers n) := by
  have hb : n*n≤base n := by unfold base;omega
  have he := (QuotientExpression.valid (numerator n i j) (denominator n) (base n)
    ((numerator_scoped n i j).mono hb) ((denominator_scoped n).mono hb)).mono (entry_subset n i j)
  apply Control.andThen_valid _ _ _ he
  have target := output_lt n i j
  simp [Control.Valid,Instruction.Valid,registers]
  omega

theorem store_literals (n : ℕ) (i j : Fin n) (B : ℕ) (hB : 1≤B) : (storeEntry n i j).LiteralsFit B := by
  apply Control.andThen_literals _ _ _ (QuotientExpression.literals _ _ _ _ hB
    (numerator_literals n i j B hB) (denominator_literals n B hB))
  have zero := (show (Parts.literal 0).Width 1 by change 0≤1 ∧ 0≤1 ∧ 1≤1;omega).mono hB
  exact ⟨zero,trivial,trivial⟩

theorem store_admissible (n : ℕ) (i j : Fin n) (v : ℕ→Parts) (hv : Good (registers n) v) :
    (storeEntry n i j).AdmissibleTrace v := by
  have hb : n*n≤base n := by unfold base;omega
  apply Control.andThen_admissible _ _ _
    (QuotientExpression.admissible (numerator n i j) (denominator n) (base n)
      ((numerator_scoped n i j).mono hb) ((denominator_scoped n).mono hb)
      (registers n) (entry_subset n i j) v hv)
  exact ⟨trivial,trivial,trivial⟩

theorem store_steps (n : ℕ) (i j : Fin n) : (storeEntry n i j).steps≤entrySteps n := by
  have hp := numerator_nodes n i j
  have hq := denominator_nodes n
  have h := QuotientExpression.control_steps (numerator n i j) (denominator n) (base n)
  simp only [storeEntry,Control.andThen_steps,Control.steps,entryControl]
  unfold QuotientExpression.steps at h
  unfold entrySteps
  omega

theorem store_result (n : ℕ) (i j : Fin n) (v : ℕ→ℚ) :
    (storeEntry n i j).rationalEvaluate v (output n i j)=(source n v).det⁻¹*(source n v).adjugate i j ∧
    ∀k,k<base n → k≠output n i j → (storeEntry n i j).rationalEvaluate v k=v k := by
  have hne : base n≠output n i j := (Nat.ne_of_lt (output_lt n i j)).symm
  have hb : n*n≤base n := by unfold base;omega
  have keep := (QuotientExpression.rational_result (numerator n i j) (denominator n) (base n)
    ((numerator_scoped n i j).mono hb) ((denominator_scoped n).mono hb) v).2
  simp only [storeEntry,Control.andThen_rational,Control.rationalEvaluate,Instruction.rationalUpdate,
    Function.update_self,Function.update_of_ne hne,zero_add,entry_value]
  refine ⟨trivial,?_⟩
  intro k hk hkt
  rw [Function.update_of_ne hkt,Function.update_of_ne hkt]
  exact keep k hk

theorem store_source (n : ℕ) (i j : Fin n) (v : ℕ→ℚ) :
    source n ((storeEntry n i j).rationalEvaluate v)=source n v := by
  apply source_eq_of_small
  intro k hk
  apply (store_result n i j v).2 k
  · unfold base;omega
  · unfold output;omega

theorem traversal_valid (n : ℕ) (xs : List (Fin n×Fin n)) : (traversal n xs).Valid (registers n) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact Control.andThen_valid _ _ _ (store_valid n x.1 x.2) ih

theorem traversal_literals (n : ℕ) (xs : List (Fin n×Fin n)) (B : ℕ) (hB : 1≤B) :
    (traversal n xs).LiteralsFit B := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact Control.andThen_literals _ _ _ (store_literals n x.1 x.2 B hB) ih

theorem traversal_admissible (n : ℕ) (xs : List (Fin n×Fin n)) (v : ℕ→Parts)
    (hv : Good (registers n) v) : (traversal n xs).AdmissibleTrace v := by
  induction xs generalizing v with
  | nil => trivial
  | cons x xs ih =>
    have a := store_admissible n x.1 x.2 v hv
    exact Control.andThen_admissible _ _ v a
      (ih _ ((storeEntry n x.1 x.2).evaluate_good _ (store_valid n x.1 x.2) v hv a))

theorem traversal_steps (n : ℕ) (xs : List (Fin n×Fin n)) :
    (traversal n xs).steps≤xs.length*entrySteps n := by
  induction xs with
  | nil => simp [traversal,Control.steps]
  | cons x xs ih =>
    have h := store_steps n x.1 x.2
    simp only [traversal,Control.andThen_steps,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem traversal_result (n : ℕ) (xs : List (Fin n×Fin n)) (v : ℕ→ℚ) :
    source n ((traversal n xs).rationalEvaluate v)=source n v ∧
    (∀p∈xs,(traversal n xs).rationalEvaluate v (output n p.1 p.2)=
      (source n v).det⁻¹*(source n v).adjugate p.1 p.2) ∧
    (∀k,k<base n → (∀p∈xs,k≠output n p.1 p.2) → (traversal n xs).rationalEvaluate v k=v k) := by
  induction xs generalizing v with
  | nil => exact ⟨rfl,by simp,fun _ _ _ => rfl⟩
  | cons x xs ih =>
    let u := (storeEntry n x.1 x.2).rationalEvaluate v
    have tail := ih u
    have same : source n u=source n v := store_source n x.1 x.2 v
    simp only [traversal,Control.andThen_rational]
    refine ⟨tail.1.trans same,?_,?_⟩
    · intro p hp
      by_cases hm : p∈xs
      · exact (tail.2.1 p hm).trans (by rw [same])
      · have hp' : p=x := by simpa only [List.mem_cons,hm,or_false] using hp
        subst p
        have preserved := tail.2.2 (output n x.1 x.2) (output_lt n x.1 x.2) (by
          intro p hpx he
          have pair : x=p := output_injective n he
          exact hm (pair.symm ▸ hpx))
        exact preserved.trans (store_result n x.1 x.2 v).1
    · intro k hk no
      exact (tail.2.2 k hk (fun p hp => no p (List.mem_cons_of_mem _ hp))).trans
        ((store_result n x.1 x.2 v).2 k hk (no x (List.mem_cons_self)))

#print axioms traversal_result
end Maxwell.Continuum.RationalDataflow.MatrixInverse
