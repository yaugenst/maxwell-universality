import Maxwell.Cost.SelectedParameters.GeometricValues
import Maxwell.Cost.SelectedParameters.LeastLoop
import Maxwell.Cost.RationalCompare

namespace Maxwell.Cost.SelectedParameters.Geometric
open Structured RationalAccumulator

def searchCode : Code := LeastLoop.code 35 RationalCompare.code (NatAssign.code advance)
def testCost (B : ℕ) : ℕ := 8000*(B+2)^2
def advanceCost (B : ℕ) : ℕ := 3000*8^5*(B+2)^2

structure Ready (a b c d n : ℕ) (s : Store) : Prop where
  bank : NatAssign.Bank ids (values a b c d n) s.val
  scratch : NatAssign.Scratch s.val

theorem test (a b c d n N A B : ℕ) (hn : n ≤ N) (hb : 0 < b) (hd : 0 < d)
    (haW : a.bits.length ≤ A) (hbW : b.bits.length ≤ A)
    (hcW : c.bits.length ≤ B) (hdW : d.bits.length ≤ B)
    (input : List Bool) (randomTape : ℕ → Bool) (s : Store) (hs : Ready a b c d n s) :
    ∃ cost t, Executes input randomTape RationalCompare.code cost s t ∧
      cost ≤ testCost (width N A B) ∧ Ready a b c d n t ∧
      t.val.registers 35 = decide (¬((a:ℚ)/b)^n ≤ (c:ℚ)/d) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  have hbank : RationalAccumulator.Bank s.val (values a b c d n) := by
    intro i hi hj
    exact hs.bank i (by
      simp only [ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      omega)
  have scratch : RationalAccumulator.Scratch s.val 0 :=
    ⟨hs.scratch 0 (by decide),(zero_word_iff_blank _ _).mpr (hs.scratch 1 (by decide)),
      hs.scratch 2 (by decide),hs.scratch 3 (by decide)⟩
  have hbits : ∀ i, 30 ≤ i → i ≤ 33 → (values a b c d n i).bits.length ≤ width N A B :=
    fun i _ _ => values_width a b c d n N A B hn haW hbW hcW hdW i
  obtain ⟨cost,t,hcost,he,ht,bt,st,ft⟩ := RationalCompare.compare input randomTape
    (values a b c d n) (width N A B) hbits
    (by simpa [values] using hd) (by simpa [values] using Nat.pow_pos hb)
    (by simp [values]) (by simp [values]) s hbank scratch
  refine ⟨cost,t,he,hcost,⟨?_,?_⟩,?_,?_⟩
  · intro i hi
    by_cases hr : 30 ≤ i ∧ i ≤ 36
    · exact bt i hr.1 hr.2
    · exact word_of_eq (ft.2.2.2.2.2.1 i (ids_ge i hi) (by omega)) (hs.bank i hi)
  · intro i hi
    interval_cases i
    · exact st.1
    · exact (zero_word_iff_blank _ _).mp st.2.1
    · exact st.2.2.1
    · exact st.2.2.2
  · simpa [values,not_le,div_pow] using ht
  · refine ⟨ft.1,ft.2.1,ft.2.2.1,ft.2.2.2.1,ft.2.2.2.2.1,?_⟩
    intro i hi
    simp only [workspace,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
    exact ft.2.2.2.2.2.1 i (by omega) (by omega)

theorem next (a b c d n N A B : ℕ) (hn : n ≤ N)
    (haW : a.bits.length ≤ A) (hbW : b.bits.length ≤ A)
    (hcW : c.bits.length ≤ B) (hdW : d.bits.length ≤ B)
    (input : List Bool) (randomTape : ℕ → Bool) (s : Store) (hs : Ready a b c d n s) :
    ∃ cost t, Executes input randomTape (NatAssign.code advance) cost s t ∧
      cost ≤ advanceCost (width N A B) ∧ Ready a b c d (n+1) t ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost,t,he,hcost,bt,st,ft⟩ := NatAssign.executes ids ids_ge advance advance_valid
    (values a b c d n) input randomTape s hs.bank hs.scratch
  have hprice := NatAssign.price_bound ids advance advance_valid (values a b c d n)
    (width N A B) (fun i _ => values_width a b c d n N A B hn haW hbW hcW hdW i)
    (by simp [advance,NatAssign.Instruction.literalWidth])
  rw [show advance.length=5 by rfl] at hprice
  exact ⟨cost,t,he,hcost.trans hprice,⟨by simpa only [advance_values] using bt,st⟩,
    ft.mono (by decide)⟩

def searchCost (N A B : ℕ) : ℕ :=
  testCost (width N A B)+1+N*(advanceCost (width N A B)+testCost (width N A B)+1)

theorem search (a b c d A B : ℕ) (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hd : 0 < d)
    (haW : a.bits.length ≤ A) (hbW : b.bits.length ≤ A)
    (hcW : c.bits.length ≤ B) (hdW : d.bits.length ≤ B)
    (input : List Bool) (randomTape : ℕ → Bool) (s : Store) (hs : Ready a b c d 0 s) :
    let rho := (a:ℚ)/b
    let target := (c:ℚ)/d
    let N := Realization.geometricSteps rho target
      (by exact div_pos (by exact_mod_cast ha) (by exact_mod_cast (ha.trans hab)))
      (by apply (div_lt_one (by exact_mod_cast (ha.trans hab))).mpr; exact_mod_cast hab)
      (by exact div_pos (by exact_mod_cast hc) (by exact_mod_cast hd))
    ∃ cost t, Executes input randomTape searchCode cost s t ∧ cost ≤ searchCost N A B ∧
      Ready a b c d N t ∧ BinaryPrecision.Frame workspace s.val t.val := by
  dsimp only
  let rho := (a:ℚ)/b
  let target := (c:ℚ)/d
  have hr : 0 < rho := div_pos (by exact_mod_cast ha) (by exact_mod_cast (ha.trans hab))
  have hr1 : rho < 1 := (div_lt_one (by exact_mod_cast (ha.trans hab))).mpr (by exact_mod_cast hab)
  have ht : 0 < target := div_pos (by exact_mod_cast hc) (by exact_mod_cast hd)
  let N := Realization.geometricSteps rho target hr hr1 ht
  let P : ℕ → Prop := fun n => rho^n ≤ target
  have hp : ∃ n, P n := ⟨N,Realization.geometricSteps_spec rho target hr hr1 ht⟩
  have hN : Nat.find hp = N := rfl
  let R : ℕ → Store → Prop := fun n t => Ready a b c d n t ∧ BinaryPrecision.Frame workspace s.val t.val
  have htest : ∀ n, n ≤ Nat.find hp → ∀ t, R n t →
      ∃ cost u, Executes input randomTape RationalCompare.code cost t u ∧
        cost ≤ testCost (width N A B) ∧ R n u ∧ u.val.registers 35=decide (¬P n) := by
    intro n hn t htr
    obtain ⟨cost,u,he,hcost,hu,htest,hf⟩ := test a b c d n N A B (hN ▸ hn)
      (ha.trans hab) hd haW hbW hcW hdW input randomTape t htr.1
    exact ⟨cost,u,he,hcost,⟨hu,htr.2.trans hf⟩,htest⟩
  have hadvance : ∀ n, n < Nat.find hp → ∀ t, R n t →
      ∃ cost u, Executes input randomTape (NatAssign.code advance) cost t u ∧
        cost ≤ advanceCost (width N A B) ∧ R (n+1) u := by
    intro n hn t htr
    obtain ⟨cost,u,he,hcost,hu,hf⟩ := next a b c d n N A B (by omega)
      haW hbW hcW hdW input randomTape t htr.1
    exact ⟨cost,u,he,hcost,hu,htr.2.trans hf⟩
  obtain ⟨cost,t,he,hcost,ht⟩ := LeastLoop.executes P hp 35 RationalCompare.code
    (NatAssign.code advance) (testCost (width N A B)) (advanceCost (width N A B))
    input randomTape R htest hadvance s ⟨hs,BinaryPrecision.Frame.refl _ _⟩
  exact ⟨cost,t,he,by simpa only [hN,searchCost] using hcost,by simpa only [hN] using ht⟩

end Maxwell.Cost.SelectedParameters.Geometric
