import Maxwell.Cost.IncidencePass.MemoryFrame
import Maxwell.Cost.IncidencePass.Read
import Maxwell.Cost.IncidencePass.Counter
import Maxwell.Cost.IncidencePass.Write
import Maxwell.Cost.IncidencePass.Cleanup

namespace Maxwell.Cost.IncidencePass
open Structured
open RationalAccumulator (Blank)
open BankArray (Word)
open Maxwell.Logical.Routing

def stepCode : Code := .seq readCode (.seq counterCode (.seq writeCode cleanupCode))

/-- The fixed Boolean program implements one complete saved-array incidence
step: two indexed reads, a copied two-bit increment, two indexed writes, and
all scratch cleanup. Its output is the existing logical routing state. -/
theorem step_executes {v i : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : IncidenceEncoding.Layout) (endpoint : Fin i → Fin v)
    (saved : IncidenceRanks.State v i) (incidence : Fin i) (index clock : List Bool)
    (hw : 0 < layout.endpointWidth) (hv : v ≤ 2 ^ layout.endpointWidth)
    (hindex : addressValue index = incidence.val) (hclock : clock.length = layout.endpointWidth)
    (hsep : layout.Separated v i) (hrank : saved.counters.get (endpoint incidence) < 3)
    (s : Store) (hconfig : Config layout index clock s.val) (hwork : Workspace s.val)
    (hrep : IncidenceEncoding.Represents layout s.val.memory endpoint saved) :
    ∃ cost t, cost ≤ 250000 * (budget layout index + 1)^2 ∧
      Executes input tape stepCode cost s t ∧ Workspace t.val ∧ Config layout index clock t.val ∧
      IncidenceEncoding.Represents layout t.val.memory endpoint (IncidenceRanks.step endpoint incidence saved) ∧
      Frame s.val t.val ∧ MemoryFrame layout v i s.val.memory t.val.memory := by
  obtain ⟨rcost, r, hrcost, er, hr88, hr89, hr90, hrs, hr7, hrm, hrc, hrf⟩ :=
    read_executes input tape layout endpoint saved incidence index clock hw hv hindex hclock
      s hconfig hwork hrep
  obtain ⟨ccost, c, hccost, ec, hc90, hcs, hcm, hkeep, hcf⟩ :=
    counter_executes input tape (saved.counters.get (endpoint incidence)) hrank r hr89 hr90 hrs
  have hc88 : Word c.val 88 (vertexWord layout endpoint incidence) :=
    BankArray.word_of_eq (hkeep 88 (by omega)) hr88
  have hc89 : Word c.val 89 (rankWord endpoint incidence saved) :=
    BankArray.word_of_eq (hkeep 89 (by omega)) hr89
  have hc7 : Blank c.val 7 := RationalAccumulator.blank_of_eq (hkeep 7 (by omega)) hr7
  have hcr : IncidenceEncoding.Represents layout c.val.memory endpoint saved := by
    simpa [hcm, hrm] using hrep
  obtain ⟨wcost, w, hwcost, ew, hws, hw7, hwm, hwkeep, hwc, hwf⟩ :=
    write_executes input tape layout endpoint saved incidence index clock hv hindex hsep c
      (hrc.of_frame hcf) hcs hc88 hc89 hc90 hcr
  obtain ⟨t, et, htw, htm, htf⟩ := cleanup_executes input tape
    (vertexWord layout endpoint incidence) (rankWord endpoint incidence saved)
    (IncidenceEncoding.word 2 (saved.counters.get (endpoint incidence) + 1)) w
    (BankArray.word_of_eq (hwkeep 88 (by omega)) hc88)
    (BankArray.word_of_eq (hwkeep 89 (by omega)) hc89)
    (BankArray.word_of_eq (hwkeep 90 (by omega)) hc90) hws
    (RationalAccumulator.blank_of_eq hw7 hc7)
  refine ⟨rcost + (ccost + (wcost +
      (6 * ((vertexWord layout endpoint incidence).length +
        (rankWord endpoint incidence saved).length +
        (IncidenceEncoding.word 2 (saved.counters.get (endpoint incidence) + 1)).length) + 12))),
    t, ?_, er.seq (ec.seq (ew.seq et)), htw, hwc.of_frame htf, ?_,
    hrf.trans (hcf.trans (hwf.trans htf)),?_⟩
  · simp only [IncidenceEncoding.word_length]
    have hb : layout.endpointWidth ≤ budget layout index := by dsimp [budget]; omega
    nlinarith
  · rw [htm, hwm]
    exact IncidenceEncoding.represents_step hcr hsep incidence

  · rw [htm,hwm,hcm,hrm]
    exact stepMemory_frame layout endpoint incidence saved s.val.memory

end Maxwell.Cost.IncidencePass
