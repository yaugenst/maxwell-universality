import Maxwell.Continuum.SourceRoutingPathPrepare

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic GeometrySort Maxwell.Logical.Routing
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem emission_one {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q))
    (level cursor : ℕ) (transpose : Bool) : emissionValues p round saved i level cursor transpose 1219=1 := by
  rw [emission_other p round saved i level cursor transpose 1219 (by decide),
    advanced_seed_other p round saved i 1219 (by decide) (by decide) (by decide)]
  rfl

theorem emission_scratch_zero {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q))
    (level cursor : ℕ) (transpose : Bool) : emissionValues p round saved i level cursor transpose 1235=0 := by
  rw [emission_other p round saved i level cursor transpose 1235 (by decide),
    advanced_seed_other p round saved i 1235 (by decide) (by decide) (by decide)]
  rfl

theorem moveColumn_lt {q parity : ℕ} (selected : RowLayer.Selection q parity) (port : Port q) :
    moveColumn port (RowLayer.movement selected port)<q := by
  cases h : RowLayer.movement selected port with
  | idle => exact port.1.isLt
  | exchange lower strand =>
    have hv:=selected.valid lower port.2.val (RowLayer.exchange_info selected port lower strand h).1
    change lower<q
    omega

theorem emission_origins {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q))
    (level cursor : ℕ) (transpose : Bool) :
    let v:=emissionValues p round saved i level cursor transpose
    let port:=finProdFinEquiv.symm i
    let col:=moveColumn port (RowLayer.movement (SortArrays.arraySelection round saved) port)
    v (axisBank 0)=16*(if transpose then port.2.val else col) ∧
      v (axisBank 1)=16*(if transpose then col else port.2.val) ∧ v (axisBank 2)=16*level := by
  have h:=origin_values transpose (pathLoaded (advanced p round saved i) level cursor)
  have column : originColumn (pathLoaded (advanced p round saved i) level cursor)=
      originColumn (advanced p round saved i) := by
    simp only [originColumn,pathLoaded_other _ _ _ 1212 (by decide) (by decide),
      pathLoaded_other _ _ _ 1213 (by decide) (by decide),pathLoaded_other _ _ _ 1203 (by decide) (by decide)]
  have row : pathLoaded (advanced p round saved i) level cursor 1204=(finProdFinEquiv.symm i).2.val := by
    rw [pathLoaded_other _ _ _ 1204 (by decide) (by decide),advanced_other p round saved i 1204 (by decide),decision_row]
    rfl
  rw [column,originColumn_advanced,row] at h
  exact h

theorem emission_coordinates_fit {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q))
    (level cursor width : ℕ) (transpose : Bool) (levelBound : level ≤ 6*q)
    (wordWidth : (1024*q+1).bits.length ≤ width) :
    ∀axis : Fin 3,((emissionValues p round saved i level cursor transpose) (axisBank axis)+64).bits.length ≤ width := by
  have h:=emission_origins p round saved i level cursor transpose
  have col:=moveColumn_lt (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i)
  have row:=(finProdFinEquiv.symm i).2.isLt
  have qp:=p.positive
  have bounds : ∀axis : Fin 3,emissionValues p round saved i level cursor transpose (axisBank axis)+64 ≤ 1024*q+1 := by
    intro axis
    have cases : axis=0 ∨ axis=1 ∨ axis=2 := by fin_cases axis <;> simp
    rcases cases with rfl|rfl|rfl
    · rw [h.1];cases transpose <;> dsimp <;> omega
    · rw [h.2.1];cases transpose <;> dsimp <;> omega
    · rw [h.2.2];omega
  exact fun axis => (Maxwell.Continuum.RationalWords.bits_mono (bounds axis)).trans wordWidth

#print axioms emission_coordinates_fit
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
