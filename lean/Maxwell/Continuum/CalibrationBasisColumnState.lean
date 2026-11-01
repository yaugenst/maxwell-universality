import Maxwell.Continuum.CalibrationBasisReentryBounds

/-! A canonical column boundary retains physical scalars and all completed
matrix entries while every source/header input is represented explicitly. -/
namespace Maxwell.Continuum.Calibration.BasisColumn
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalDataflow PartArray ArrayDecodeMachine NeumannMachine BasisForcing
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
attribute [local irreducible] BasisForcing.bank SchurRow.nodeCount

structure State (R heap P : ℕ) (p : ℕ→Parts) (s : Store) : Prop where
  ready : BasisReentry.InputReady R heap p s
  good : Good BasisScalarReload.bank (BasisScalarReload.values p)
  width : WidthBank BasisScalarReload.bank P (BasisScalarReload.values p)

def inputWidth (R heap P : ℕ) : ℕ := 103+R.bits.length+heap.bits.length+P

theorem State.schur_good {R heap P : ℕ} {p : ℕ→Parts} {s : Store} (h : State R heap P p s) :
    Good SchurRow.bank p := by
  intro i hi
  simpa only [BasisScalarReload.schur_values p i hi] using h.good i (Finset.mem_union_right _ hi)

theorem State.schur_width {R heap P : ℕ} {p : ℕ→Parts} {s : Store} (h : State R heap P p s) :
    WidthBank SchurRow.bank P p := by
  intro i hi
  simpa only [BasisScalarReload.schur_values p i hi] using h.width i (Finset.mem_union_right _ hi)

theorem State.schur_cells {R heap P : ℕ} {p : ℕ→Parts} {s : Store} (h : State R heap P p s) :
    Cells SchurRow.bank p s.val := by
  intro i hi
  simpa only [BasisScalarReload.schur_values p i hi] using
    Cells.of_ready h.ready.parts i (Finset.mem_union_right _ hi)

theorem source_mem (i : ℕ) (hi : i∈retained) : i∈BasisForcing.bank := by
  have low:=Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
  simpa only [BasisForcing.bank,Finset.mem_range] using (show i<232 by omega)

theorem State.natural_width {R heap P : ℕ} {p : ℕ→Parts} {s : Store} (h : State R heap P p s) :
    ∀k∈allocationIds,(BasisReentry.numbers R heap p k).bits.length≤ inputWidth R heap P := by
  intro k hk
  unfold BasisReentry.numbers
  split_ifs with rad free
  · unfold inputWidth;omega
  · unfold inputWidth;omega
  · by_cases cell : k∈ids BasisForcing.bank
    · exact (dataValues_width BasisForcing.bank _ P
        (fun i hi=>h.width i (Finset.mem_union_left _ hi)) k cell).trans (by unfold inputWidth;omega)
    · have low : k<1000 := by
        rcases Finset.mem_union.mp hk with natural | allocator
        · rcases Finset.mem_union.mp natural with main | quotient
          · rcases Finset.mem_union.mp main with raw | decoder
            · exact (cell raw).elim
            · simp only [ArrayDecodeMachine.ports,Finset.mem_Icc] at decoder;omega
          · simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at quotient;omega
        · simp only [Finset.mem_insert,Finset.mem_singleton] at allocator;omega
      rw [dataValues_small _ low]
      exact Nat.zero_le _

theorem quasi_values (p : ℕ→Parts) (j : Fin 3) :
    RawFree.quasiParts (BasisScalarReload.values p) j=p (234+j.val) := by
  have values:=BasisScalarReload.source_values p
  fin_cases j
  · exact values.2.2.1
  · exact values.2.2.2.1
  · exact values.2.2.2.2

def matrix (R : ℕ) (p : ℕ→Parts) : Matrix (Fin 24) (Fin 24) ℚ :=
  cachedSchurMatrix (p 232).value (p 233).value (fun j=>(p (234+j.val)).value) (R-2)

def admissible (p : ℕ→Parts) : Prop :=
  (3:ℝ)≤(p 232).value ∧ (7:ℝ)≤(p 233).value ∧ ((p 233).value:ℝ)≤8 ∧
    ∀j:Fin 3,|((p (234+j.val)).value:ℝ)|≤1/16

#print axioms State.natural_width
#print axioms quasi_values
end Maxwell.Continuum.Calibration.BasisColumn
