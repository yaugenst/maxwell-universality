import Maxwell.Continuum.RationalDataflowWordReplace
import Maxwell.Cost.WordSwap

/-! A fixed finite plan swaps runtime metadata words by actual move
programs. The temporary word is cleared again and every move is charged. -/
namespace Maxwell.Continuum.RationalDataflow.WordSwapPlan
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def values (left right : ℕ) (v : ℕ→List Bool) : ℕ→List Bool :=
  Function.update (Function.update v left (v right)) right (v left)

def evaluate : List (ℕ×ℕ)→(ℕ→List Bool)→(ℕ→List Bool)
  | [],v => v
  | (left,right)::rest,v => evaluate rest (values left right v)

def code (temp : ℕ) : List (ℕ×ℕ)→Code
  | [] => .skip
  | (left,right)::rest => .seq (WordSwap.code left right temp) (code temp rest)

def Bank (S : Finset ℕ) (v : ℕ→List Bool) (s : BitRAMState) : Prop :=
  ∀i∈S,BankArray.Word s i (v i)

theorem values_width {S : Finset ℕ} {W left right : ℕ} (v : ℕ→List Bool)
    (hl : left∈S) (hr : right∈S) (hv : ∀i∈S,(v i).length≤W) :
    ∀i∈S,(values left right v i).length≤W := by
  intro i hi
  by_cases hy : i=right
  · subst i; simpa only [values,Function.update_self] using hv left hl
  by_cases hx : i=left
  · subst i; simpa only [values,Function.update_of_ne hy,Function.update_self] using hv right hr
  simpa only [values,Function.update_of_ne hy,Function.update_of_ne hx] using hv i hi

theorem executes (S : Finset ℕ) (temp W : ℕ) (ht : temp∉S)
    (plan : List (ℕ×ℕ)) (hp : ∀x∈plan,x.1∈S ∧ x.2∈S ∧ x.1≠x.2)
    (v : ℕ→List Bool) (hv : ∀i∈S,(v i).length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : Bank S v s.val) (hz : RationalAccumulator.Blank s.val temp) :
    ∃ cost t, Executes input tape (code temp plan) cost s t ∧
      cost≤plan.length*(36*W+33)+1 ∧ Bank S (evaluate plan v) t.val ∧
      (∀i∈S,(evaluate plan v i).length≤W) ∧ RationalAccumulator.Blank t.val temp ∧
      BinaryPrecision.Frame (insert temp S) s.val t.val := by
  induction plan generalizing v s with
  | nil => exact ⟨1,s,.skip s,by simp,hb,hv,hz,BinaryPrecision.Frame.refl _ _⟩
  | cons x rest ih =>
    have hx := hp x (by simp)
    have hxt : x.1≠temp := by intro he; exact ht (he ▸ hx.1)
    have hyt : x.2≠temp := by intro he; exact ht (he ▸ hx.2.1)
    obtain ⟨r,er,hrl,hrr,hz',fr⟩ := WordSwap.executes x.1 x.2 temp hx.2.2 hxt hyt
      input tape (v x.1) (v x.2) s (hb x.1 hx.1) (hb x.2 hx.2.1) hz
    have hbank : Bank S (values x.1 x.2 v) r.val := by
      intro i hi
      by_cases hy : i=x.2
      · subst i; simpa only [values,Function.update_self] using hrr
      by_cases hl : i=x.1
      · subst i; simpa only [values,Function.update_of_ne hy,Function.update_self] using hrl
      have hit : i≠temp := by intro he; exact ht (he ▸ hi)
      simpa only [values,Function.update_of_ne hy,Function.update_of_ne hl] using
        BankArray.word_of_eq (fr.2.2.2.2.2.1 i hl hy hit) (hb i hi)
    have hwidth := values_width v hx.1 hx.2.1 hv
    obtain ⟨cost,t,ex,hcost,bank,width,blank,frame⟩ := ih
      (fun y hy => hp y (by simp [hy])) (values x.1 x.2 v) hwidth r hbank hz'
    have f : BinaryPrecision.Frame (insert temp S) s.val r.val := by
      refine ⟨fr.1,fr.2.1,fr.2.2.1,fr.2.2.2.1,fr.2.2.2.2.1,?_⟩
      intro i hi
      have his : i∉S := fun h => hi (Finset.mem_insert_of_mem h)
      apply fr.2.2.2.2.2.1 i
      · intro he; exact his (he ▸ hx.1)
      · intro he; exact his (he ▸ hx.2.1)
      · intro he; exact hi (by simp [he])
    refine ⟨(12*(2*(v x.1).length+(v x.2).length)+33)+cost,t,er.seq ex,?_,bank,width,blank,f.trans frame⟩
    have hl := hv x.1 hx.1
    have hr := hv x.2 hx.2.1
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

#print axioms executes
end Maxwell.Continuum.RationalDataflow.WordSwapPlan
