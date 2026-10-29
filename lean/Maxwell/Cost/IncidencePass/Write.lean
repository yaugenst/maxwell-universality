import Maxwell.Cost.IncidencePass.Read
import Maxwell.Cost.BankArray.Write

namespace Maxwell.Cost.IncidencePass
open Structured
open RationalAccumulator (Blank)
open BankArray (Word)
open Maxwell.Logical.Routing

def writeCode : Code := .seq (BankArray.writeCode 84 88 85 90) (BankArray.writeCode 84 81 86 89)

/-- The two charged writes update the saved counter and rank arrays in the
same order as `IncidenceEncoding.stepMemory`. -/
theorem write_executes {v i : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : IncidenceEncoding.Layout) (endpoint : Fin i → Fin v)
    (saved : IncidenceRanks.State v i) (incidence : Fin i) (index clock : List Bool)
    (hv : v ≤ 2 ^ layout.endpointWidth) (hindex : addressValue index = incidence.val)
    (hsep : layout.Separated v i) (s : Store) (hconfig : Config layout index clock s.val)
    (hs : BankArray.Scratch s.val)
    (h88 : Word s.val 88 (vertexWord layout endpoint incidence))
    (h89 : Word s.val 89 (rankWord endpoint incidence saved))
    (h90 : Word s.val 90 (IncidenceEncoding.word 2 (saved.counters.get (endpoint incidence) + 1)))
    (hrep : IncidenceEncoding.Represents layout s.val.memory endpoint saved) :
    ∃ cost t, cost ≤ 60000 * (budget layout index + 1)^2 ∧
      Executes input tape writeCode cost s t ∧ BankArray.Scratch t.val ∧
      t.val.tapes 7 = s.val.tapes 7 ∧
      t.val.memory = IncidenceEncoding.stepMemory layout endpoint incidence saved s.val.memory ∧
      (∀ j, j = 4 ∨ 10 ≤ j → t.val.tapes j = s.val.tapes j) ∧
      Config layout index clock t.val ∧ Frame s.val t.val := by
  let rank := saved.counters.get (endpoint incidence)
  obtain ⟨costC, c, hcostC, ec, hcm, _, hcs, hc7, hcf⟩ :=
    BankArray.write_bank 84 88 85 90 (by omega) (by omega) (by omega) (by omega)
      input tape (2 : ℕ).bits (vertexWord layout endpoint incidence) layout.baseCounter.bits
      (IncidenceEncoding.word 2 (rank + 1)) (IncidenceEncoding.words 2 saved.counters) (endpoint incidence)
      (by decide) (IncidenceEncoding.word_value _ _ (lt_of_lt_of_le (endpoint incidence).isLt hv))
      (by simp) s hs hconfig.two h88 hconfig.counters h90 (by simpa using hrep.counters)
  have cf := Frame.of_bank hcf
  have cc := hconfig.of_frame cf
  have c89 : Word c.val 89 (rankWord endpoint incidence saved) :=
    BankArray.word_of_eq (hcf.2.2.2.1 89 (by omega)) h89
  have cranks : BitArray.Represents c.val.memory layout.baseRank 2 (IncidenceEncoding.words 2 saved.ranks) := by
    rw [hcm]
    simpa only [addressValue_bits] using IncidenceEncoding.represents_write_disjoint hrep.ranks
      layout.baseCounter 2 (endpoint incidence) (IncidenceEncoding.word 2 (rank + 1))
      (by simp) hsep.counterRank.symm
  obtain ⟨costR, t, hcostR, et, htm, _, hts, ht7, htf⟩ :=
    BankArray.write_bank 84 81 86 89 (by omega) (by omega) (by omega) (by omega)
      input tape (2 : ℕ).bits index layout.baseRank.bits (rankWord endpoint incidence saved)
      (IncidenceEncoding.words 2 saved.ranks) incidence (by decide) hindex (by simp)
      c hcs cc.two cc.index cc.ranks c89 (by simpa using cranks)
  have tf := Frame.of_bank htf
  have ff := cf.trans tf
  refine ⟨costC + costR, t, ?_, ec.seq et, hts, ht7.trans hc7, ?_,
    fun j hj => (htf.2.2.2.1 j hj).trans (hcf.2.2.2.1 j hj), hconfig.of_frame ff, ff⟩
  · let B := budget layout index
    have hbC := array_cost_le (2 : ℕ).bits (vertexWord layout endpoint incidence)
      layout.baseCounter.bits (IncidenceEncoding.word 2 (rank + 1)) B
      (by change 2 ≤ B; dsimp [B, budget]; omega)
      (by simp only [IncidenceEncoding.word_length]; dsimp [B, budget]; omega)
      (by dsimp [B, budget]; omega)
      (by simp only [IncidenceEncoding.word_length]; dsimp [B, budget]; omega)
      (by simp only [addressValue_bits]; dsimp [B, budget]; omega)
    have hbR := array_cost_le (2 : ℕ).bits index layout.baseRank.bits (rankWord endpoint incidence saved) B
      (by change 2 ≤ B; dsimp [B, budget]; omega) (by dsimp [B, budget]; omega)
      (by dsimp [B, budget]; omega)
      (by simp only [IncidenceEncoding.word_length]; dsimp [B, budget]; omega)
      (by simp only [addressValue_bits]; dsimp [B, budget]; omega)
    dsimp only [B] at hbC hbR
    omega
  · rw [htm, hcm]
    simp only [addressValue_bits, IncidenceEncoding.stepMemory, rank]

end Maxwell.Cost.IncidencePass
