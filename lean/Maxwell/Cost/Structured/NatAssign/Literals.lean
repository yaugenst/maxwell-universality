import Maxwell.Cost.Structured.NatAssign.Values

/-! Initialize any finite stored natural bank by actual literal writes.
The same program clears and replaces bounded old words on repeated calls. -/
namespace Maxwell.Cost.Structured.NatAssign.Literals
open RationalAccumulator (Blank)

def plan (ids : Finset ℕ) (v : ℕ→ℕ) : List Instruction :=
  (ids.sort (·≤·)).map (fun i=>.literal i (v i))
def code (ids : Finset ℕ) (v : ℕ→ℕ) : Code := NatAssign.code (plan ids v)
def cost (ids : Finset ℕ) (B : ℕ) : ℕ := 3000*8^ids.card*(B+2)^2

theorem valid (ids : Finset ℕ) (v : ℕ→ℕ) : ∀a∈plan ids v,a.Valid ids := by
  intro a ha
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp ha
  simpa only [Finset.mem_sort,Instruction.Valid] using hi

theorem executes (ids : Finset ℕ) (hids : ∀i∈ids,4≤ i) (v old : ℕ→ℕ) (B : ℕ)
    (width : ∀i∈ids,(v i).bits.length≤B) (oldWidth : ∀i∈ids,(old i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : Bank ids old s.val) (scratch : Scratch s.val) :
    ∃steps t,Executes input tape (code ids v) steps s t ∧ steps≤cost ids B ∧
      Bank ids v t.val ∧ Scratch t.val ∧ BinaryPrecision.Frame ({0,1,2,3}∪ids) s.val t.val := by
  obtain ⟨c,t,e,charge,stored,blank,frame⟩:=NatAssign.executes ids hids (plan ids v)
    (valid ids v) old input tape s bank scratch
  refine ⟨c,t,e,?_,?_,blank,frame.mono ?_⟩
  · apply charge.trans
    have bound:=price_bound ids (plan ids v) (valid ids v) old B oldWidth (by
      intro a ha
      obtain ⟨i,hi,rfl⟩:=List.mem_map.mp ha
      exact width i (by simpa only [Finset.mem_sort] using hi))
    simpa only [plan,List.length_map,Finset.length_sort,cost] using bound
  · intro i hi
    simpa only [plan,values_literals,Finset.mem_sort,ite_eq_left hi] using stored i hi
  · intro i hi
    rcases Finset.mem_union.mp hi with low|assigned
    · exact Finset.mem_union_left _ low
    · obtain ⟨a,ha,target⟩:=List.mem_map.mp (List.mem_toFinset.mp assigned)
      obtain ⟨j,hj,rfl⟩:=List.mem_map.mp ha
      exact Finset.mem_union_right _ (target ▸ (by simpa only [Finset.mem_sort,Instruction.target] using hj))

theorem fresh_executes (ids : Finset ℕ) (hids : ∀i∈ids,4≤ i) (v : ℕ→ℕ) (B : ℕ)
    (width : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (fresh : ∀i∈ids,Blank s.val i) (scratch : Scratch s.val) :
    ∃steps t,Executes input tape (code ids v) steps s t ∧ steps≤cost ids B ∧
      Bank ids v t.val ∧ Scratch t.val ∧ BinaryPrecision.Frame ({0,1,2,3}∪ids) s.val t.val :=
  executes ids hids v (fun _=>0) B width (by simp) input tape s
    (fun i hi=>(RationalAccumulator.zero_word_iff_blank _ _).mpr (fresh i hi)) scratch

#print axioms executes
end Maxwell.Cost.Structured.NatAssign.Literals
