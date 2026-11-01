import Maxwell.Continuum.RationalDataflowPartsCopy

/-! A fixed family of raw rational copies reuses one word-bank contract.
The list order is explicit, so overlapping copies have their actual semantics. -/
namespace Maxwell.Continuum.RationalDataflow.PartsCopies
open Maxwell.Cost Maxwell.Cost.Structured

def code : List (ℕ×ℕ)→Code
  | [] => .skip
  | (source,target)::rest => .seq (partsCopyCode source target) (code rest)
def values : List (ℕ×ℕ)→(ℕ→Parts)→(ℕ→Parts)
  | [],v => v
  | (source,target)::rest,v => values rest (Function.update v target (v source))

theorem keep (pairs : List (ℕ×ℕ)) (v : ℕ→Parts) (i : ℕ)
    (outside : ∀p∈pairs,i≠p.2) : values pairs v i=v i := by
  induction pairs generalizing v with
  | nil => rfl
  | cons p rest ih =>
    rw [values,ih _ (fun q hq=>outside q (List.mem_cons_of_mem _ hq)),
      Function.update_of_ne (outside p (by simp))]

theorem good (pairs : List (ℕ×ℕ)) (S : Finset ℕ)
    (sources : ∀p∈pairs,p.1∈S) (v : ℕ→Parts) (hg : Good S v) : Good S (values pairs v) := by
  induction pairs generalizing v with
  | nil => exact hg
  | cons p rest ih =>
    apply ih (fun q hq=>sources q (List.mem_cons_of_mem _ hq))
    exact hg.update p.2 (hg p.1 (sources p (by simp)))

theorem executes (pairs : List (ℕ×ℕ)) (S : Finset ℕ)
    (valid : ∀p∈pairs,p.1∈S ∧ p.2∈S ∧ p.1≠p.2)
    (v : ℕ→Parts) (B : ℕ) (width : WidthBank S B v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (ready : Ready S v s) :
    ∃steps t,Executes input tape (code pairs) steps s t ∧
      steps ≤ pairs.length*stageCost B+1 ∧ Ready S (values pairs v) t ∧
      WidthBank S B (values pairs v) ∧ BinaryPrecision.Frame (workspace S) s.val t.val := by
  induction pairs generalizing v s with
  | nil => exact ⟨1,s,.skip s,by simp,ready,width,BinaryPrecision.Frame.refl _ _⟩
  | cons p rest ih =>
    have pair:=valid p (by simp)
    obtain ⟨c0,u,e0,b0,r0,w0,f0⟩:=partsCopy_executes S p.1 p.2 pair.1 pair.2.1 pair.2.2
      v B width input tape s ready
    obtain ⟨c1,t,e1,b1,r1,w1,f1⟩:=ih (fun q hq=>valid q (List.mem_cons_of_mem _ hq)) _ w0 u r0
    refine ⟨c0+c1,t,e0.seq e1,?_,r1,w1,f0.trans f1⟩
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

#print axioms executes
end Maxwell.Continuum.RationalDataflow.PartsCopies
