import Maxwell.Cost.ArrayAccess
import Maxwell.Cost.Structured.AddressWidth
import Maxwell.Cost.MemoryWord.Width
import Maxwell.Cost.MemoryWord.WriteWidth

namespace Maxwell.Cost.ArrayAccess
open Structured

/-- A bit-length bound derived from the actual stored arithmetic operands
and the finite number of consecutive memory accesses. -/
def addressWidth (s : BitRAMState) (width index base payload : List Bool) : ℕ :=
  max s.address.length (width.length+index.length+base.length+1+payload.length)

theorem read_visited (input : List Bool) (tape : ℕ→Bool)
    (width index base clock : List Bool) (ao wo zo yo io bo savedOrigin clockOrigin : ℤ)
    (hwidth : 0<width.length) (s t : Store)
    (hready : Ready s.val width index base ao wo zo yo io bo savedOrigin)
    (h6 : s.val.tapes 6=BitTape.shifted clock clockOrigin)
    (cost : ℕ) (run : Executes input tape readCode cost s t) :
    Visited (addressWidth s.val width index base clock) input tape readCode cost s t := by
  obtain ⟨acost,a,_,_,addressOrigin,_,_,ha,_,_,_,_,ha5,_,_,haf⟩ :=
    IndexedAddress.executes input tape width index base ao wo zo yo io bo savedOrigin hwidth s
      hready.zero hready.width hready.scratch hready.multiply hready.index hready.base hready.saved
  let W := addressWidth s.val width index base clock
  let address := (addressValue base+addressValue width*addressValue index).bits
  have hA : Visited W input tape IndexedAddress.code acost s a :=
    ha.visited_noAddressPush (by decide) (le_max_left _ _)
  have ha6 : a.val.tapes 6=BitTape.shifted clock clockOrigin :=
    (haf.2.2.2.2.2.1 6 (by omega) (by omega) (by omega)).trans h6
  have hb : address.length+clock.length≤W := by
    have h := address_length_le width index base
    exact (Nat.add_le_add_right h clock.length).trans (le_max_right _ _)
  obtain ⟨rcost,r,_,hr,hrpc⟩ := MemoryWord.loop_visited input tape clock address addressOrigin
    address.length W a.val le_rfl hb hA.finish a.property ha5
    (ha6 ▸ BitTape.shifted_represents clock clockOrigin)
  have hR : Visited W input tape (.call MemoryWord.readProgram) (rcost+1) a (Store.ofState r) :=
    .call _ a r rcost hr (by rw [hrpc]; rfl)
  exact (hA.seq hR).of_execution run

theorem write_visited (input : List Bool) (tape : ℕ→Bool)
    (width index base word : List Bool) (ao wo zo yo io bo savedOrigin wordOrigin : ℤ)
    (hwidth : 0<width.length) (s t : Store)
    (hready : Ready s.val width index base ao wo zo yo io bo savedOrigin)
    (h6 : s.val.tapes 6=BitTape.shifted word wordOrigin)
    (cost : ℕ) (run : Executes input tape writeCode cost s t) :
    Visited (addressWidth s.val width index base word) input tape writeCode cost s t := by
  obtain ⟨acost,a,_,_,addressOrigin,_,_,ha,_,_,_,_,ha5,_,_,haf⟩ :=
    IndexedAddress.executes input tape width index base ao wo zo yo io bo savedOrigin hwidth s
      hready.zero hready.width hready.scratch hready.multiply hready.index hready.base hready.saved
  let W := addressWidth s.val width index base word
  let address := (addressValue base+addressValue width*addressValue index).bits
  have hA : Visited W input tape IndexedAddress.code acost s a :=
    ha.visited_noAddressPush (by decide) (le_max_left _ _)
  have ha6 : a.val.tapes 6=BitTape.shifted word wordOrigin :=
    (haf.2.2.2.2.2.1 6 (by omega) (by omega) (by omega)).trans h6
  have hb : address.length+word.length≤W := by
    have h := address_length_le width index base
    exact (Nat.add_le_add_right h word.length).trans (le_max_right _ _)
  obtain ⟨rcost,r,_,hr,hrpc⟩ := MemoryWord.write_loop_visited input tape word address addressOrigin
    address.length W a.val le_rfl hb hA.finish a.property ha5
    (ha6 ▸ BitTape.shifted_represents word wordOrigin)
  have hR : Visited W input tape (.call MemoryWord.writeProgram) (rcost+1) a (Store.ofState r) :=
    .call _ a r rcost hr (by rw [hrpc]; rfl)
  exact (hA.seq hR).of_execution run

end Maxwell.Cost.ArrayAccess
