import Maxwell.Cost.RationalCanonical.StoredEmission
import Maxwell.Cost.Structured.WordCleanupBounds

/-! A fixed list of stored fractions shares one measured serializer
workspace. The executable list contains only tape identifiers. -/
namespace Maxwell.Cost.RationalCanonical.StoredEmission
open Structured RationalAccumulator
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def listCode : List (ℕ×ℕ×ℕ)→Code
  | [] => .skip
  | (p,n,d)::rest => .seq (code p n d) (listCode rest)

def listBits (ports : List (ℕ×ℕ×ℕ)) (v : ℕ→ℕ) : List Bool :=
  ports.flatMap (fun (p,n,d)=>Codec.rat (((v p:ℚ)-v n)/v d))

theorem list_executes (ports : List (ℕ×ℕ×ℕ)) (v : ℕ→ℕ) (B H : ℕ)
    (hH : B+1 ≤ H)
    (lower : ∀a∈ports,232 ≤ a.1 ∧232 ≤ a.2.1 ∧232 ≤ a.2.2)
    (positive : ∀a∈ports,0<v a.2.2)
    (width : ∀a∈ports,(v a.1).bits.length ≤ B ∧
      (v a.2.1).bits.length ≤ B ∧(v a.2.2).bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : ∀a∈ports,Word s.val a.1 (v a.1) ∧Word s.val a.2.1 (v a.2.1) ∧
      Word s.val a.2.2 (v a.2.2)) (old : WordCleanup.Bounded words H s.val)
    (scratch : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape (listCode ports) cost s t ∧
      cost ≤ ports.length*costBound B H+1 ∧
      t.val.output=(listBits ports v).reverse++s.val.output ∧
      WordCleanup.Bounded words H t.val ∧NatAssign.Scratch t.val ∧
      t.val.address=s.val.address ∧t.val.memory=s.val.memory ∧
      t.val.inputHead=s.val.inputHead ∧t.val.randomCursor=s.val.randomCursor ∧
      (∀i,i∉work→t.val.tapes i=s.val.tapes i) := by
  induction ports generalizing s with
  | nil => exact ⟨1,s,.skip s,by simp,by simp [listBits],old,scratch,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
  | cons entry rest ih =>
    obtain ⟨p,n,d⟩:=entry
    have lo:=lower (p,n,d) (by simp)
    have w:=width (p,n,d) (by simp)
    have b:=bank (p,n,d) (by simp)
    change (v p).bits.length ≤ B ∧(v n).bits.length ≤ B ∧(v d).bits.length ≤ B at w
    obtain ⟨c,a,e,hc,out,ready,addr,mem,inp,rng,keep⟩:=executes p n d (v p) (v n) (v d) B H
      lo.1 lo.2.1 lo.2.2 (positive (p,n,d) (by simp)) w.1 w.2.1 w.2.2 input tape s b.1 b.2.1 b.2.2 old
    have oldA : WordCleanup.Bounded words H a.val:=bounded ready
      ((IntegerNormSquare.magnitude_bits_length_le _ _).trans (by omega)) (w.2.2.trans (by omega))
    have bankA : ∀entry∈rest,Word a.val entry.1 (v entry.1) ∧
        Word a.val entry.2.1 (v entry.2.1) ∧Word a.val entry.2.2 (v entry.2.2) := by
      intro entry he
      have low:=lower entry (List.mem_cons_of_mem _ he)
      have stored:=bank entry (List.mem_cons_of_mem _ he)
      have preserved (i : ℕ) (hi : 232 ≤ i) : a.val.tapes i=s.val.tapes i:=keep i (by
        simp only [work,words,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
        omega)
      exact ⟨word_of_eq (preserved _ low.1) stored.1,word_of_eq (preserved _ low.2.1) stored.2.1,
        word_of_eq (preserved _ low.2.2) stored.2.2⟩
    obtain ⟨c1,t,e1,hc1,out1,oldT,scratchT,addr1,mem1,inp1,rng1,keep1⟩:=ih
      (fun e he=>lower e (List.mem_cons_of_mem _ he))
      (fun e he=>positive e (List.mem_cons_of_mem _ he))
      (fun e he=>width e (List.mem_cons_of_mem _ he)) a bankA oldA (fun i hi=>ready.work.scratch i (by omega))
    refine ⟨c+c1,t,e.seq e1,?_,?_,oldT,scratchT,addr1.trans addr,mem1.trans mem,inp1.trans inp,rng1.trans rng,
      fun i hi=>(keep1 i hi).trans (keep i hi)⟩
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · rw [out1,out]
      simp only [listBits,List.flatMap_cons,List.reverse_append,List.append_assoc]

#print axioms list_executes
end Maxwell.Cost.RationalCanonical.StoredEmission
