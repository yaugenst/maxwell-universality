import Maxwell.Cost.BankArray.ReadBank
import Maxwell.Cost.BankArray.Write
import Maxwell.Cost.IncidenceEncoding

namespace Maxwell.Cost.IncidencePass
open Structured
open RationalAccumulator (Blank)
open BankArray (Word)
open Maxwell.Logical.Routing

/-- Persistent descriptors for the three saved arrays. -/
structure Config (layout : IncidenceEncoding.Layout) (index clock : List Bool) (s : BitRAMState) : Prop where
  width : Word s 80 layout.endpointWidth.bits
  index : Word s 81 index
  endpoints : Word s 82 layout.baseEndpoint.bits
  clock : Word s 83 clock
  two : Word s 84 (2 : ℕ).bits
  counters : Word s 85 layout.baseCounter.bits
  ranks : Word s 86 layout.baseRank.bits
  twoClock : Word s 87 [false, false]

/-- The finite body may alter only its three private bank words. -/
def Frame (s t : BitRAMState) : Prop :=
  t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i = 4 ∨ 10 ≤ i → i ≠ 88 → i ≠ 89 → i ≠ 90 → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 →
    t.registers i = s.registers i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  rcases h with ⟨hi, hr, ho, ht, hg⟩
  rcases k with ⟨ki, kr, ko, kt, kg⟩
  exact ⟨ki.trans hi, kr.trans hr, ko.trans ho,
    fun i hh h88 h89 h90 => (kt i hh h88 h89 h90).trans (ht i hh h88 h89 h90),
    fun i h15 h24 h25 h26 h27 h28 h29 =>
      (kg i h15 h24 h25 h26 h27 h28 h29).trans (hg i h15 h24 h25 h26 h27 h28 h29)⟩

theorem Frame.of_bank {s t : BitRAMState} (h : BankArray.Frame s t) : Frame s t :=
  ⟨h.1, h.2.1, h.2.2.1, fun i hi _ _ _ => h.2.2.2.1 i hi, h.2.2.2.2⟩

theorem Frame.of_except {bank : ℕ} {s t : BitRAMState}
    (hb : bank = 88 ∨ bank = 89 ∨ bank = 90) (h : BankArray.FrameExcept bank s t) : Frame s t :=
  ⟨h.1, h.2.1, h.2.2.1, fun i hi h88 h89 h90 => h.2.2.2.1 i hi (by omega), h.2.2.2.2⟩

theorem Frame.of_transfer {source target : ℕ} {s t : BitRAMState}
    (hs : source = 88 ∨ source = 89 ∨ source = 90)
    (ht : target = 88 ∨ target = 89 ∨ target = 90)
    (h : WordTransfer.Frame source target s t) : Frame s t := by
  rcases h with ⟨_, hi, _, hr, ho, tapes, regs⟩
  exact ⟨hi, hr, ho, fun i _ h88 h89 h90 => tapes i (by omega) (by omega),
    fun i _ h24 h25 h26 h27 _ _ => regs i h24 h25 h26 h27⟩

theorem Config.of_frame {layout : IncidenceEncoding.Layout} {index clock : List Bool}
    {s t : BitRAMState} (h : Frame s t) (c : Config layout index clock s) : Config layout index clock t := by
  constructor
  · exact BankArray.word_of_eq (h.2.2.2.1 80 (by omega) (by omega) (by omega) (by omega)) c.width
  · exact BankArray.word_of_eq (h.2.2.2.1 81 (by omega) (by omega) (by omega) (by omega)) c.index
  · exact BankArray.word_of_eq (h.2.2.2.1 82 (by omega) (by omega) (by omega) (by omega)) c.endpoints
  · exact BankArray.word_of_eq (h.2.2.2.1 83 (by omega) (by omega) (by omega) (by omega)) c.clock
  · exact BankArray.word_of_eq (h.2.2.2.1 84 (by omega) (by omega) (by omega) (by omega)) c.two
  · exact BankArray.word_of_eq (h.2.2.2.1 85 (by omega) (by omega) (by omega) (by omega)) c.counters
  · exact BankArray.word_of_eq (h.2.2.2.1 86 (by omega) (by omega) (by omega) (by omega)) c.ranks
  · exact BankArray.word_of_eq (h.2.2.2.1 87 (by omega) (by omega) (by omega) (by omega)) c.twoClock

def Workspace (s : BitRAMState) : Prop :=
  BankArray.Scratch s ∧ Blank s 7 ∧ Blank s 88 ∧ Blank s 89 ∧ Blank s 90

/-- All descriptor lengths and endpoint payload width are counted explicitly. -/
def budget (layout : IncidenceEncoding.Layout) (index : List Bool) : ℕ :=
  layout.endpointWidth + layout.endpointWidth.bits.length + index.length +
    layout.baseEndpoint.bits.length + layout.baseCounter.bits.length + layout.baseRank.bits.length + 10

theorem array_cost_le (width index base payload : List Bool) (B : ℕ)
    (hw : width.length ≤ B) (hi : index.length ≤ B) (hb : base.length ≤ B)
    (hp : payload.length ≤ B) (hv : addressValue width ≤ B) :
    BankArray.costCap width index base payload ≤ 30000 * (B + 1)^2 := by
  unfold BankArray.costCap ArrayAccess.costCap
  calc
    _ ≤ 1000 * (B + B + B + 5)^2 +
        B * (15 * (B + B + B + 1 + B) + 24) + 4 + 40 * (B + B + B + B + B + 3) := by
      gcongr
    _ ≤ 30000 * (B + 1)^2 := by nlinarith

end Maxwell.Cost.IncidencePass
