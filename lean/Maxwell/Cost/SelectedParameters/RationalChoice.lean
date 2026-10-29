import Maxwell.Cost.SelectedParameters.RationalBasic
import Maxwell.Cost.SelectedParameters.Compare

/-! Minimum and maximum use the runtime rational comparator and a fixed
branch that copies the selected stored numerator and denominator. -/
namespace Maxwell.Cost.SelectedParameters.Rational
open Structured RationalAccumulator
set_option maxHeartbeats 1500000

inductive Choice where
  | minimum | maximum
  deriving DecidableEq, Repr

def choose : Choice → Bool → Bool
  | .minimum,b => b
  | .maximum,b => !b

def choicePair (op : Choice) (a b c d : ℕ) : ℕ × ℕ :=
  if choose op (decide ((a:ℚ)/b < (c:ℚ)/d)) then (a,b) else (c,d)

def choiceValue : Choice → ℚ → ℚ → ℚ
  | .minimum,a,b => min a b
  | .maximum,a,b => max a b

theorem choice_value (op : Choice) (a b c d : ℕ) :
    value (choicePair op a b c d) = choiceValue op ((a:ℚ)/b) ((c:ℚ)/d) := by
  by_cases h : (a:ℚ)/b < (c:ℚ)/d
  · cases op <;> simp [choicePair,choose,value,choiceValue,h,min_eq_left h.le,max_eq_right h.le]
  · cases op <;> simp [choicePair,choose,value,choiceValue,h,min_eq_right (le_of_not_gt h),
      max_eq_left (le_of_not_gt h)]

theorem choice_denominator (op : Choice) (a b c d : ℕ) (hb : 0 < b) (hd : 0 < d) :
    0 < (choicePair op a b c d).2 := by
  unfold choicePair
  split <;> assumption

theorem choice_width (op : Choice) (a b c d B : ℕ)
    (ha : a.bits.length ≤ B) (hb : b.bits.length ≤ B)
    (hc : c.bits.length ≤ B) (hd : d.bits.length ≤ B) :
    (choicePair op a b c d).1.bits.length ≤ B ∧ (choicePair op a b c d).2.bits.length ≤ B := by
  unfold choicePair
  split <;> exact ⟨by assumption,by assumption⟩

def choiceTail (left : Bool) (num den : ℕ) : List NatAssign.Instruction :=
  [.copy (if left then 30 else 32) num,.copy (if left then 31 else 33) den] ++ clear

def choiceCode (op : Choice) (a b c d num den : ℕ) : Code :=
  .seq (Compare.code a b c d)
    (.branch 35 (NatAssign.code (choiceTail (choose op true) num den))
      (NatAssign.code (choiceTail (choose op false) num den)))

private theorem tail_values (left : Bool) (num den : ℕ) (hn : 540 ≤ num) (v : ℕ → ℕ) :
    NatAssign.values (choiceTail left num den) v =
      after v num den (if left then (v 30,v 31) else (v 32,v 33)) := by
  have h31 : 31 ≠ num := by omega
  have h33 : 33 ≠ num := by omega
  cases left <;>
    simp [choiceTail,after,clean,clear,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,h31,h33]

private theorem after_prepare (a b c d num den : ℕ) (v : ℕ → ℕ) (p : ℕ × ℕ) :
    after (NatAssign.values (Compare.prepare a b c d) v) num den p = after v num den p := by
  ext i
  by_cases hi : i ∈ common
  · simp [after,hi]
  · have h30 : i ≠ 30 := by intro h; subst i; exact hi (by simp [common])
    have h31 : i ≠ 31 := by intro h; subst i; exact hi (by simp [common])
    have h32 : i ≠ 32 := by intro h; subst i; exact hi (by simp [common])
    have h33 : i ≠ 33 := by intro h; subst i; exact hi (by simp [common])
    simp [after,hi,Compare.prepare,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,Function.update_apply,h30,h31,h32,h33]

def choiceCostBound (B : ℕ) : ℕ :=
  3000*8^4*(B+2)^2+8000*(B+2)^2+1+3000*8^9*(B+2)^2

theorem choice_executes (extra : Finset ℕ) (hextra : ∀ i ∈ extra, 540 ≤ i)
    (op : Choice) (a b c d num den : ℕ)
    (ha : a ∈ extra) (hb : b ∈ extra) (hc : c ∈ extra) (hd : d ∈ extra)
    (hnum : num ∈ extra) (hden : den ∈ extra) (_hne : num ≠ den)
    (v : ℕ → ℕ) (B : ℕ) (hwidth : ∀ i ∈ ids extra, (v i).bits.length ≤ B)
    (hbpos : 0 < v b) (hdpos : 0 < v d) (h35 : v 35 = 0) (h36 : v 36 = 0)
    (input : List Bool) (randomTape : ℕ → Bool) (s : Store)
    (hbank : NatAssign.Bank (ids extra) v s.val) (hscratch : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input randomTape (choiceCode op a b c d num den) cost s t ∧
      cost ≤ choiceCostBound B ∧
      NatAssign.Bank (ids extra) (after v num den (choicePair op (v a) (v b) (v c) (v d))) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame (workspace num den) s.val t.val := by
  have hex40 : ∀ i ∈ extra, 40 ≤ i := fun i hi => (by omega : 40 ≤ 540).trans (hextra i hi)
  obtain ⟨c1,u,e1,p1,flag,b1,s1,f1⟩ := Compare.executes extra hex40 a b c d ha hb hc hd
    v B hwidth hbpos hdpos h35 h36 input randomTape s hbank hscratch
  let w := NatAssign.values (Compare.prepare a b c d) v
  have hw := Compare.prepared a b c d (hex40 a ha) (hex40 b hb) (hex40 c hc) (hex40 d hd) v
  have w30 : w 30 = v a := by simp [w,hw]
  have w31 : w 31 = v b := by simp [w,hw]
  have w32 : w 32 = v c := by simp [w,hw]
  have w33 : w 33 = v d := by simp [w,hw]
  have wb : ∀ i ∈ ids extra, (w i).bits.length ≤ B := by
    intro i hi
    simp only [w,hw,Function.update_apply]
    split_ifs <;> first
      | exact hwidth d (Finset.mem_union_left _ hd)
      | exact hwidth c (Finset.mem_union_left _ hc)
      | exact hwidth b (Finset.mem_union_left _ hb)
      | exact hwidth a (Finset.mem_union_left _ ha)
      | exact hwidth i hi
  let lt : Bool := decide ((v a:ℚ)/v b < (v c:ℚ)/v d)
  let left := choose op lt
  have hids : ∀ i ∈ ids extra, 4 ≤ i := by
    intro i hi
    simp only [ids,common,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with hi | hi
    · exact (by omega : 4 ≤ 540).trans (hextra i hi)
    · omega
  have hn := hextra num hnum
  have he := hextra den hden
  have hv : ∀ inst ∈ choiceTail left num den, inst.Valid (ids extra) := by
    cases left <;> simp [choiceTail,clear,NatAssign.Instruction.Valid,ids,common,hnum,hden] <;> omega
  obtain ⟨c2,t,e2,p2,b2,s2,f2⟩ := NatAssign.executes (ids extra) hids
    (choiceTail left num den) hv w input randomTape u b1 s1
  have ev : NatAssign.values (choiceTail left num den) w =
      after v num den (choicePair op (v a) (v b) (v c) (v d)) := by
    rw [tail_values left num den hn w]
    simp only [w30,w31,w32,w33]
    exact after_prepare a b c d num den v _
  have eb : Executes input randomTape
      (.branch 35 (NatAssign.code (choiceTail (choose op true) num den))
        (NatAssign.code (choiceTail (choose op false) num den))) (1+c2) u t := by
    cases hlt : lt
    · apply Executes.no (flag.trans hlt)
      simpa only [left,hlt] using e2
    · apply Executes.yes (flag.trans hlt)
      simpa only [left,hlt] using e2
  have fc : Compare.workspace ⊆ workspace num den := by
    intro i hi
    simp only [Compare.workspace,workspace,common,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton] at hi ⊢
    omega
  have ft : NatAssign.changes (choiceTail left num den) ⊆ workspace num den := by
    intro i hi
    cases left <;>
      simp [NatAssign.changes,choiceTail,clear,NatAssign.Instruction.target,workspace,common] at hi ⊢ <;> omega
  refine ⟨c1+(1+c2),t,e1.seq eb,?_,ev ▸ b2,s2,(f1.mono fc).trans (f2.mono ft)⟩
  have hp := NatAssign.price_bound (ids extra) (choiceTail left num den) hv w B wb
    (by cases left <;> simp [choiceTail,clear,NatAssign.Instruction.literalWidth])
  rw [show (choiceTail left num den).length = 9 by cases left <;> rfl] at hp
  have htail := p2.trans hp
  dsimp only [choiceCostBound]
  omega

end Maxwell.Cost.SelectedParameters.Rational
