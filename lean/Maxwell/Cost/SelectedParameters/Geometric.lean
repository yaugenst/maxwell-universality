import Maxwell.Cost.SelectedParameters.GeometricCore

namespace Maxwell.Cost.SelectedParameters.Geometric
open Structured RationalAccumulator

def code : Code := .seq (NatAssign.code initialization) searchCode
def initialCost (B : ℕ) : ℕ := 3000*8^11*(B+2)^2

def exponent (a b c d : ℕ) (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hd : 0 < d) : ℕ :=
  Realization.geometricSteps ((a:ℚ)/b) ((c:ℚ)/d)
    (div_pos (by exact_mod_cast ha) (by exact_mod_cast (ha.trans hab)))
    ((div_lt_one (by exact_mod_cast (ha.trans hab))).mpr (by exact_mod_cast hab))
    (div_pos (by exact_mod_cast hc) (by exact_mod_cast hd))

theorem initialize_executes (v : ℕ → ℕ) (B : ℕ) (hB : 1 ≤ B)
    (hwidth : ∀ i ∈ ids, (v i).bits.length ≤ B)
    (input : List Bool) (randomTape : ℕ → Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hs : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input randomTape (NatAssign.code initialization) cost s t ∧
      cost ≤ initialCost B ∧ Ready (v 520) (v 521) (v 522) (v 523) 0 t ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost,t,he,hcost,bt,st,ft⟩ := NatAssign.executes ids ids_ge initialization
    initialization_valid v input randomTape s hb hs
  have hp := NatAssign.price_bound ids initialization initialization_valid v B hwidth
    (by simp [initialization,NatAssign.Instruction.literalWidth,hB])
  rw [show initialization.length=11 by rfl] at hp
  refine ⟨cost,t,he,hcost.trans hp,⟨?_,st⟩,ft.mono (by decide)⟩
  intro i hi
  have hh := bt i hi
  simpa only [initialization_values v i hi] using hh

/-- One fixed finite program selects the least exponent by exact rational
tests. Its input is four stored words, and it physically initializes every
power, counter, comparison slot, and constant used by the search. -/
theorem executes (v : ℕ → ℕ) (A B : ℕ) (hB : 1 ≤ B)
    (ha : 0 < v 520) (hab : v 520 < v 521) (hc : 0 < v 522) (hd : 0 < v 523)
    (hwidth : ∀ i ∈ ids, (v i).bits.length ≤ B)
    (haW : (v 520).bits.length ≤ A) (hbW : (v 521).bits.length ≤ A)
    (input : List Bool) (randomTape : ℕ → Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hs : NatAssign.Scratch s.val) :
    let N := exponent (v 520) (v 521) (v 522) (v 523) ha hab hc hd
    ∃ cost t, Executes input randomTape code cost s t ∧
      cost ≤ initialCost B+searchCost N A B ∧ Ready (v 520) (v 521) (v 522) (v 523) N t ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c1,u,e1,p1,h1,f1⟩ := initialize_executes v B hB hwidth input randomTape s hb hs
  obtain ⟨c2,t,e2,p2,h2,f2⟩ := search (v 520) (v 521) (v 522) (v 523) A B ha hab hc hd
    haW hbW (hwidth 522 (by decide)) (hwidth 523 (by decide)) input randomTape u h1
  exact ⟨c1+c2,t,e1.seq e2,Nat.add_le_add p1 p2,h2,f1.trans f2⟩

theorem run (v : ℕ → ℕ) (A B : ℕ) (hB : 1 ≤ B)
    (ha : 0 < v 520) (hab : v 520 < v 521) (hc : 0 < v 522) (hd : 0 < v 523)
    (hwidth : ∀ i ∈ ids, (v i).bits.length ≤ B)
    (haW : (v 520).bits.length ≤ A) (hbW : (v 521).bits.length ≤ A)
    (input : List Bool) (randomTape : ℕ → Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hs : NatAssign.Scratch s.val) :
    let N := exponent (v 520) (v 521) (v 522) (v 523) ha hab hc hd
    let cap := initialCost B+searchCost N A B
    ∃ t : Store, (runPriced (code.compile.next input randomTape) (cap+1) s.val).finished =
        some (t.place code.size) ∧
      (runPriced (code.compile.next input randomTape) (cap+1) s.val).instructions ≤ cap ∧
      Word t.val 526 N ∧ Word t.val 524 ((v 520)^N) ∧ Word t.val 525 ((v 521)^N) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost,t,he,hcost,ht,hf⟩ := executes v A B hB ha hab hc hd hwidth haW hbW
    input randomTape s hb hs
  let N := exponent (v 520) (v 521) (v 522) (v 523) ha hab hc hd
  let cap := initialCost B+searchCost N A B
  have hr := he.compiled_run (cap+1) (Nat.lt_succ_of_le hcost)
  refine ⟨t,hr.1,hr.2 ▸ hcost,?_,?_,?_,hf⟩
  · simpa [values] using ht.bank 526 (by decide)
  · simpa [values] using ht.bank 524 (by decide)
  · simpa [values] using ht.bank 525 (by decide)

end Maxwell.Cost.SelectedParameters.Geometric
