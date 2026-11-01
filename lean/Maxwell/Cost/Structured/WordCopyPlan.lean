import Maxwell.Cost.WordReplace
import Maxwell.Cost.BinaryPrecision

/-! Fixed plans copy arbitrary finite stored words, including padded words.
Every overwrite and every copied bit is charged; only target tapes change. -/
namespace Maxwell.Cost.Structured.WordCopyPlan
set_option maxHeartbeats 2500000

def evaluate : List (ℕ×ℕ)→(ℕ→List Bool)→(ℕ→List Bool)
  | [],v => v
  | (source,target)::rest,v => evaluate rest (Function.update v target (v source))

def code : List (ℕ×ℕ)→Code
  | [] => .skip
  | (source,target)::rest => .seq (WordReplace.code source target) (code rest)

def targets (plan : List (ℕ×ℕ)) : Finset ℕ := (plan.map Prod.snd).toFinset

def Bank (S : Finset ℕ) (v : ℕ→List Bool) (s : BitRAMState) : Prop :=
  ∀i∈S,BankArray.Word s i (v i)

theorem executes (S : Finset ℕ) (W : ℕ) (plan : List (ℕ×ℕ))
    (hp : ∀x∈plan,x.1∈S ∧ x.2∈S ∧ x.1≠x.2)
    (v : ℕ→List Bool) (hv : ∀i∈S,(v i).length ≤ W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hb : Bank S v s.val) :
    ∃cost t,Executes input tape (code plan) cost s t ∧
      cost ≤ plan.length*(21*W+21)+1 ∧ Bank S (evaluate plan v) t.val ∧
      (∀i∈S,(evaluate plan v i).length ≤ W) ∧ BinaryPrecision.Frame (targets plan) s.val t.val := by
  induction plan generalizing v s with
  | nil => exact ⟨1,s,.skip s,by simp,hb,hv,BinaryPrecision.Frame.refl _ _⟩
  | cons x rest ih =>
    have hx := hp x (by simp)
    obtain ⟨u,e0,word,f0⟩ := WordReplace.executes x.1 x.2 hx.2.2 input tape
      (v x.1) (v x.2) s (hb x.1 hx.1) (hb x.2 hx.2.1)
    have bank : Bank S (Function.update v x.2 (v x.1)) u.val := by
      intro i hi
      by_cases he:i=x.2
      · subst i;simpa only [Function.update_self] using word
      · simpa only [Function.update_of_ne he] using BankArray.word_of_eq (f0.2.2.2.2.2.1 i he) (hb i hi)
    have width : ∀i∈S,(Function.update v x.2 (v x.1) i).length ≤ W := by
      intro i hi
      by_cases he:i=x.2
      · subst i;simpa only [Function.update_self] using hv x.1 hx.1
      · simpa only [Function.update_of_ne he] using hv i hi
    obtain ⟨c,t,e1,hc,bank1,width1,f1⟩ := ih (fun y hy=>hp y (by simp [hy])) _ width u bank
    have targetEq : targets (x::rest)=insert x.2 (targets rest) := by simp [targets]
    have frame0 : BinaryPrecision.Frame (targets (x::rest)) s.val u.val := by
      refine ⟨f0.1,f0.2.1,f0.2.2.1,f0.2.2.2.1,f0.2.2.2.2.1,?_⟩
      intro i hi
      apply f0.2.2.2.2.2.1 i
      intro he
      exact hi (by rw [targetEq,he];exact Finset.mem_insert_self _ _)
    have frame1 := f1.mono (show targets rest⊆targets (x::rest) by rw [targetEq];exact Finset.subset_insert _ _)
    refine ⟨(6*(v x.2).length+15*(v x.1).length+21)+c,t,e0.seq e1,?_,bank1,width1,frame0.trans frame1⟩
    have hs := hv x.1 hx.1
    have ht := hv x.2 hx.2.1
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

#print axioms executes
end Maxwell.Cost.Structured.WordCopyPlan
