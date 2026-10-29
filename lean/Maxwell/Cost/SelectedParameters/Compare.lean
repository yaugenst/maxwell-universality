import Maxwell.Cost.Structured.NatAssign.Bounds
import Maxwell.Cost.RationalCompare

/-! Charged rational comparison of four stored natural-number words.
The numerator/denominator source tapes are read at runtime; only their
addresses occur in the finite program. -/
namespace Maxwell.Cost.SelectedParameters
open Structured RationalAccumulator
namespace Compare

def workspace : Finset ℕ := {0,1,2,3,30,31,32,33,34,35,36}

def prepare (a b c d : ℕ) : List NatAssign.Instruction :=
  [.copy a 30,.copy b 31,.copy c 32,.copy d 33]

def code (a b c d : ℕ) : Code :=
  .seq (NatAssign.code (prepare a b c d)) RationalCompare.code

def ids (extra : Finset ℕ) : Finset ℕ := extra ∪ {30,31,32,33,34,35,36}

theorem prepared (a b c d : ℕ) (_ha : 40 ≤ a) (hb : 40 ≤ b)
    (hc : 40 ≤ c) (hd : 40 ≤ d) (v : ℕ → ℕ) :
    NatAssign.values (prepare a b c d) v =
      Function.update (Function.update (Function.update (Function.update v 30 (v a))
        31 (v b)) 32 (v c)) 33 (v d) := by
  simp [prepare,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,show b≠30 by omega,show c≠30 by omega,show c≠31 by omega,
    show d≠30 by omega,show d≠31 by omega,show d≠32 by omega]

theorem executes (extra : Finset ℕ) (hextra : ∀ i ∈ extra, 40 ≤ i)
    (a b c d : ℕ) (ha : a ∈ extra) (hb : b ∈ extra) (hc : c ∈ extra) (hd : d ∈ extra)
    (v : ℕ → ℕ) (B : ℕ) (hwidth : ∀ i ∈ ids extra, (v i).bits.length ≤ B)
    (hbpos : 0 < v b) (hdpos : 0 < v d) (h35 : v 35 = 0) (h36 : v 36 = 0)
    (input : List Bool) (randomTape : ℕ → Bool) (s : Store)
    (hbank : NatAssign.Bank (ids extra) v s.val) (hscratch : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input randomTape (code a b c d) cost s t ∧
      cost ≤ 3000*8^4*(B+2)^2+8000*(B+2)^2 ∧
      t.val.registers 35 = decide ((v a : ℚ)/v b < (v c : ℚ)/v d) ∧
      NatAssign.Bank (ids extra) (NatAssign.values (prepare a b c d) v) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame workspace s.val t.val := by
  have ha40 := hextra a ha
  have hb40 := hextra b hb
  have hc40 := hextra c hc
  have hd40 := hextra d hd
  have hids : ∀ i ∈ ids extra, 4 ≤ i := by
    intro i hi
    simp only [ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with hi | hi
    · exact (by omega : 4 ≤ 40).trans (hextra i hi)
    · omega
  have hvalid : ∀ inst ∈ prepare a b c d, inst.Valid (ids extra) := by
    intro inst hi
    simp only [prepare,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [NatAssign.Instruction.Valid,ids,ha,hb,hc,hd] <;> omega
  obtain ⟨c1,u,e1,p1,b1,s1,f1⟩ := NatAssign.executes (ids extra) hids
    (prepare a b c d) hvalid v input randomTape s hbank hscratch
  let w := NatAssign.values (prepare a b c d) v
  have hw := prepared a b c d ha40 hb40 hc40 hd40 v
  have w30 : w 30 = v a := by simp [w,hw]
  have w31 : w 31 = v b := by simp [w,hw]
  have w32 : w 32 = v c := by simp [w,hw]
  have w33 : w 33 = v d := by simp [w,hw]
  have w35 : w 35 = 0 := by simp [w,hw,h35]
  have w36 : w 36 = 0 := by simp [w,hw,h36]
  have wb : RationalAccumulator.Bank u.val w := by
    intro i hi hj
    apply b1 i
    simp only [ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    omega
  have ws : RationalAccumulator.Scratch u.val 0 :=
    ⟨s1 0 (by decide),(zero_word_iff_blank _ _).mpr (s1 1 (by decide)),
      s1 2 (by decide),s1 3 (by decide)⟩
  have hwa := hwidth a (Finset.mem_union_left _ ha)
  have hwb := hwidth b (Finset.mem_union_left _ hb)
  have hwc := hwidth c (Finset.mem_union_left _ hc)
  have hwd := hwidth d (Finset.mem_union_left _ hd)
  have wbits : ∀ i, 30 ≤ i → i ≤ 33 → (w i).bits.length ≤ B := by
    intro i hi hj
    interval_cases i
    · simpa only [w30] using hwa
    · simpa only [w31] using hwb
    · simpa only [w32] using hwc
    · simpa only [w33] using hwd
  obtain ⟨c2,t,p2,e2,ht,bt,st,ft⟩ := RationalCompare.compare input randomTape w B
    wbits (by rw [w31]; exact hbpos) (by rw [w33]; exact hdpos) w35 w36 u wb ws
  have fw : BinaryPrecision.Frame workspace u.val t.val := by
    refine ⟨ft.1,ft.2.1,ft.2.2.1,ft.2.2.2.1,ft.2.2.2.2.1,?_⟩
    intro i hi
    simp only [workspace,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
    exact ft.2.2.2.2.2.1 i (by omega) (by omega)
  refine ⟨c1+c2,t,e1.seq e2,?_,by simpa only [w30,w31,w32,w33] using ht,?_,?_,
    (f1.mono (by
      change ({0,1,2,3} ∪ {30,31,32,33}) ⊆ workspace
      decide)).trans fw⟩
  · have hp := NatAssign.price_bound (ids extra) (prepare a b c d) hvalid v B hwidth
      (by intro inst hi; simp only [prepare,List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl <;> simp [NatAssign.Instruction.literalWidth])
    rw [show (prepare a b c d).length=4 by rfl] at hp
    exact Nat.add_le_add (p1.trans hp) p2
  · intro i hi
    by_cases h30 : 30 ≤ i ∧ i ≤ 36
    · exact bt i h30.1 h30.2
    · exact word_of_eq (ft.2.2.2.2.2.1 i (hids i hi) (by omega)) (b1 i hi)
  · intro i hi
    interval_cases i
    · exact st.1
    · exact (zero_word_iff_blank _ _).mp st.2.1
    · exact st.2.2.1
    · exact st.2.2.2

end Compare
end Maxwell.Cost.SelectedParameters
