import Maxwell.Cost.IncidencePass.Common

namespace Maxwell.Cost.IncidencePass
open Structured
open RationalAccumulator (Blank)
open BankArray (Word)
open Maxwell.Logical.Routing

abbrev vertexWord (layout : IncidenceEncoding.Layout) {v i : ℕ}
    (endpoint : Fin i → Fin v) (incidence : Fin i) : List Bool :=
  IncidenceEncoding.word layout.endpointWidth (endpoint incidence).val

abbrev rankWord {v i : ℕ} (endpoint : Fin i → Fin v) (incidence : Fin i)
    (saved : IncidenceRanks.State v i) : List Bool :=
  IncidenceEncoding.word 2 (saved.counters.get (endpoint incidence))

def readCode : Code := .seq (BankArray.readBankCode 80 81 82 83 88)
  (BankArray.readBankCode 84 88 85 87 89)

/-- The finite incidence body reads its cached endpoint and its saved counter.
Both results are stored once, with all array accesses and address arithmetic charged. -/
theorem read_executes {v i : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : IncidenceEncoding.Layout) (endpoint : Fin i → Fin v)
    (saved : IncidenceRanks.State v i) (incidence : Fin i) (index clock : List Bool)
    (hw : 0 < layout.endpointWidth) (hv : v ≤ 2 ^ layout.endpointWidth)
    (hindex : addressValue index = incidence.val) (hclock : clock.length = layout.endpointWidth)
    (s : Store) (hconfig : Config layout index clock s.val) (hwork : Workspace s.val)
    (hrep : IncidenceEncoding.Represents layout s.val.memory endpoint saved) :
    ∃ cost t, cost ≤ 70000 * (budget layout index + 1)^2 ∧
      Executes input tape readCode cost s t ∧
      Word t.val 88 (vertexWord layout endpoint incidence) ∧
      Word t.val 89 (rankWord endpoint incidence saved) ∧ Blank t.val 90 ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧
      t.val.memory = s.val.memory ∧ Config layout index clock t.val ∧ Frame s.val t.val := by
  rcases hwork with ⟨hs, h7, h88, h89, h90⟩
  obtain ⟨costE, e, hcostE, ee, he88, hes, he7, hem, _, hef⟩ :=
    BankArray.read_bank 80 81 82 83 88 (by omega) (by omega) (by omega) (by omega) (by omega)
      input tape layout.endpointWidth.bits index layout.baseEndpoint.bits clock
      (IncidenceEncoding.words layout.endpointWidth (IncidenceEncoding.endpointValues endpoint)) incidence
      (RationalAccumulator.bits_nonempty hw) hindex (by simpa using hclock) s hs h7 h88
      hconfig.width hconfig.index hconfig.endpoints hconfig.clock
      (by simpa using hrep.endpoints)
  have ef : Frame s.val e.val := Frame.of_except (Or.inl rfl) hef
  have ec := hconfig.of_frame ef
  have e89 : Blank e.val 89 := RationalAccumulator.blank_of_eq
    (hef.2.2.2.1 89 (by omega) (by omega)) h89
  have he88' : Word e.val 88 (vertexWord layout endpoint incidence) := by simpa using he88
  obtain ⟨costC, t, hcostC, et, ht89, hts, ht7, htm, _, htf⟩ :=
    BankArray.read_bank 84 88 85 87 89 (by omega) (by omega) (by omega) (by omega) (by omega)
      input tape (2 : ℕ).bits (vertexWord layout endpoint incidence) layout.baseCounter.bits [false, false]
      (IncidenceEncoding.words 2 saved.counters) (endpoint incidence) (by decide)
      (IncidenceEncoding.word_value _ _ (lt_of_lt_of_le (endpoint incidence).isLt hv))
      (by decide) e hes he7 e89 ec.two he88' ec.counters ec.twoClock
      (by simpa [hem] using hrep.counters)
  have tf : Frame e.val t.val := Frame.of_except (Or.inr (Or.inl rfl)) htf
  have allFrame := ef.trans tf
  refine ⟨costE + costC, t, ?_, ee.seq et,
    BankArray.word_of_eq (htf.2.2.2.1 88 (by omega) (by omega)) he88',
    by simpa using ht89,
    RationalAccumulator.blank_of_eq ((htf.2.2.2.1 90 (by omega) (by omega)).trans
      (hef.2.2.2.1 90 (by omega) (by omega))) h90,
    hts, ht7, htm.trans hem, hconfig.of_frame allFrame, allFrame⟩
  let B := budget layout index
  have hbE := array_cost_le layout.endpointWidth.bits index layout.baseEndpoint.bits clock B
    (by dsimp [B, budget]; omega) (by dsimp [B, budget]; omega)
    (by dsimp [B, budget]; omega) (by dsimp [B, budget]; omega)
    (by simp only [addressValue_bits]; dsimp [B, budget]; omega)
  have hbC := array_cost_le (2 : ℕ).bits (vertexWord layout endpoint incidence)
    layout.baseCounter.bits [false, false] B
    (by change 2 ≤ B; dsimp [B, budget]; omega)
    (by simp only [IncidenceEncoding.word_length]; dsimp [B, budget]; omega)
    (by dsimp [B, budget]; omega) (by change 2 ≤ B; dsimp [B, budget]; omega)
    (by simp only [addressValue_bits]; dsimp [B, budget]; omega)
  have hwidthB : layout.endpointWidth ≤ B := by dsimp [B, budget]; omega
  simp only [addressValue_bits] at hcostE hcostC
  dsimp only [B] at hbE hbC hwidthB
  nlinarith

end Maxwell.Cost.IncidencePass
