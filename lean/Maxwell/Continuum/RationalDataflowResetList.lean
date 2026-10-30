import Maxwell.Continuum.RationalDataflowControlResults

/-! A fixed list of rational work registers is reset through actual
literal-write instructions, with no growth of the width invariant. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def resetList : List ℕ→Control
  | [] => .done
  | i::rest => .step (.literal i 0) (resetList rest)

theorem resetList_values (xs : List ℕ) (v : ℕ→Parts) (i : ℕ) :
    (resetList xs).evaluate v i=if i∈xs then Parts.literal 0 else v i := by
  induction xs generalizing v with
  | nil => simp [resetList,Control.evaluate]
  | cons k rest ih =>
    simp only [resetList,Control.evaluate,Instruction.update,ih,List.mem_cons]
    by_cases hik : i=k <;> by_cases hir : i∈rest <;> simp [hik,hir]

theorem resetList_valid (S : Finset ℕ) (xs : List ℕ) (hxs : ∀i∈xs,i∈S) :
    (resetList xs).Valid S := by
  induction xs with
  | nil => trivial
  | cons k rest ih =>
    exact ⟨hxs k (by simp),ih (fun i hi => hxs i (List.mem_cons_of_mem _ hi))⟩

theorem resetList_steps (xs : List ℕ) : (resetList xs).steps=xs.length := by
  induction xs with
  | nil => rfl
  | cons k rest ih => simp [resetList,Control.steps,ih,Nat.add_comm]

theorem resetList_width (S : Finset ℕ) (xs : List ℕ) (v : ℕ→Parts) (B : ℕ)
    (hB : 1≤B) (hv : WidthBank S B v) : (resetList xs).WidthTrace S B v := by
  induction xs generalizing v with
  | nil => exact hv
  | cons k rest ih =>
    have hz : (Parts.literal 0).Width B :=
      (show (Parts.literal 0).Width 1 by norm_num [Parts.Width,Parts.literal]).mono hB
    exact ⟨hv,hz,ih _ (hv.update k hz)⟩

theorem resetList_admissible (xs : List ℕ) (v : ℕ→Parts) :
    (resetList xs).AdmissibleTrace v := by
  induction xs generalizing v with
  | nil => trivial
  | cons k rest ih => exact ⟨trivial,ih _⟩

theorem resetList_executes (S : Finset ℕ) (xs : List ℕ) (hxs : ∀i∈xs,i∈S)
    (v : ℕ→Parts) (B : ℕ) (hB : 1≤B) (hv : WidthBank S B v) (hg : Good S v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) :
    ∃cost t,Executes input tape (resetList xs).code cost s t ∧
      cost≤xs.length*operationCost B+1 ∧ Ready S ((resetList xs).evaluate v) t ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  simpa only [resetList_steps] using (resetList xs).executes S (resetList_valid S xs hxs)
    v B (resetList_width S xs v B hB hv) hg (resetList_admissible xs v) input tape s hs

#print axioms resetList_executes
end Maxwell.Continuum.RationalDataflow
