import Maxwell.Continuum.SourceRoutingTerminalPrepare

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open GeometryArithmetic Maxwell.Logical.Routing
set_option maxRecDepth 16384
set_option maxHeartbeats 2600000

theorem terminal_one {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ) (port : Port q) (cursor : ℕ) (bottom : Bool) :
    terminalValues p round port cursor bottom 1219=1 := by
  rw [terminal_other p round port cursor bottom 1219 (by decide)]
  rfl

theorem terminal_scratch_zero {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ) (port : Port q) (cursor : ℕ) (bottom : Bool) :
    terminalValues p round port cursor bottom 1235=0 := by
  rw [terminal_other p round port cursor bottom 1235 (by decide)]
  rfl

theorem terminal_cursor {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ) (port : Port q) (cursor : ℕ) (bottom : Bool) :
    terminalValues p round port cursor bottom 1234=cursor := by
  rw [terminal_other p round port cursor bottom 1234 (by decide)]
  rfl

theorem terminal_coordinates_fit {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ) (port : Port q)
    (cursor width : ℕ) (bottom : Bool) (wordWidth : (1024*q+1).bits.length ≤ width) :
    ∀axis : Fin 3,(terminalValues p round port cursor bottom (axisBank axis)+64).bits.length ≤ width := by
  have h := terminal_values p round port cursor bottom
  have col := port.1.isLt
  have row := port.2.isLt
  have qp := p.positive
  have bounded : ∀axis : Fin 3,terminalValues p round port cursor bottom (axisBank axis)+64 ≤ 1024*q+1 := by
    intro axis
    have cases : axis=0 ∨ axis=1 ∨ axis=2 := by fin_cases axis <;> simp
    rcases cases with rfl|rfl|rfl
    · rw [h.1];cases bottom <;> dsimp <;> omega
    · rw [h.2.1];cases bottom <;> dsimp <;> omega
    · rw [h.2.2];cases bottom <;> dsimp <;> omega
  exact fun axis => (Maxwell.Continuum.RationalWords.bits_mono (bounded axis)).trans wordWidth

theorem bottom_origin {half : ℕ} (p : GeometrySort.Plan (2*half)) (round : ℕ)
    (tile : Port half) (arm : Fin 3) (cursor : ℕ) :
    bankOrigin (terminalValues p round (Gluing.tilePort tile arm) cursor true)=
      ((32 : ℤ)*tile.1.val,(32 : ℤ)*tile.2.val,0) := by
  have h := terminal_values p round (Gluing.tilePort tile arm) cursor true
  rw [bankOrigin,h.1,h.2.1,h.2.2]
  fin_cases arm <;> simp [Gluing.tilePort,Nat.add_div]

theorem bottom_selects {half : ℕ} (p : GeometrySort.Plan (2*half)) (round : ℕ)
    (tile : Port half) (arm : Fin 3) (cursor : ℕ) (part : Bool) :
    (bottomChoice part).evaluate (terminalValues p round (Gluing.tilePort tile arm) cursor true)=.bottom part arm := by
  have h := terminal_selectors p round (Gluing.tilePort tile arm) cursor
  apply bottomChoice_evaluate
  · rw [h.1]
    fin_cases arm <;> simp [Gluing.tilePort]
  · rw [h.2]
    fin_cases arm <;> simp [Gluing.tilePort]

theorem top_origin {half : ℕ} (p : GeometrySort.Plan (2*half)) (round : ℕ)
    (pair : Fin half × Fin (2*half)) (cursor : ℕ) :
    bankOrigin (terminalValues p round (Gluing.pairPort pair false) cursor false)=
      ((32 : ℤ)*pair.1.val,(16 : ℤ)*pair.2.val,(96 : ℤ)*(2*half)) := by
  have h := terminal_values p round (Gluing.pairPort pair false) cursor false
  rw [bankOrigin,h.1,h.2.1,h.2.2]
  simp only [Bool.false_eq_true,ite_false,Gluing.pairPort,Nat.add_zero,Nat.cast_mul,Nat.cast_ofNat]
  congr 1; ring

theorem endpoint_origin {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ) (port : Port q) (cursor : ℕ) :
    bankOrigin (terminalValues p round port cursor false)=Schedule.gridPort port (96*q) := by
  have h := terminal_values p round port cursor false
  simp only [Bool.false_eq_true,ite_false] at h
  simp only [bankOrigin,h.1,h.2.1,h.2.2,Schedule.gridPort,Nat.cast_mul,Nat.cast_ofNat]

#print axioms bottom_selects
#print axioms top_origin
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
