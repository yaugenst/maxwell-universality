import Maxwell.Continuum.CalibrationBasisColumnMachine

/-! The fixed24-column program constructs its Schur matrix from physical
input scalars. Each iteration regenerates the source and inverse and performs
charged cleanup before the next column. No supplied matrix table is used. -/
namespace Maxwell.Continuum.Calibration.BasisMatrix
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
attribute [local irreducible] BasisForcing.bank SchurRow.nodeCount

def code : List (Fin 24)→Code
  | [] => .skip
  | column::rest => .seq (BasisColumn.code column) (code rest)

private theorem scalar_kept (column : Fin 24) (p out : ℕ→Parts)
    (kept : ∀i,(i<240 ∨ 384 ≤ i)→i<1200→(∀row,i≠SchurRow.output row column)→ out i=p i)
    (i : ℕ) (low : i<240) : out i=p i := by
  apply kept i (Or.inl low) (by omega)
  intro row
  have bound:=SchurRow.output_bounds row column
  omega

private theorem matrix_kept (column : Fin 24) (R : ℕ) (p out : ℕ→Parts)
    (kept : ∀i,(i<240 ∨ 384 ≤ i)→i<1200→(∀row,i≠SchurRow.output row column)→ out i=p i) :
    BasisColumn.matrix R out=BasisColumn.matrix R p := by
  have quasi : (fun j:Fin 3=>(out (234+j.val)).value)=(fun j:Fin 3=>(p (234+j.val)).value) := by
    funext j
    rw [scalar_kept column p out kept _ (by omega)]
  simp only [BasisColumn.matrix,scalar_kept column p out kept 232 (by decide),
    scalar_kept column p out kept 233 (by decide),quasi]

private theorem physical_kept (column : Fin 24) (p out : ℕ→Parts)
    (kept : ∀i,(i<240 ∨ 384 ≤ i)→i<1200→(∀row,i≠SchurRow.output row column)→ out i=p i)
    (physical : BasisColumn.admissible p) : BasisColumn.admissible out := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [scalar_kept column p out kept 232 (by decide)] using physical.1
  · simpa only [scalar_kept column p out kept 233 (by decide)] using physical.2.1
  · simpa only [scalar_kept column p out kept 233 (by decide)] using physical.2.2.1
  · intro j
    simpa only [scalar_kept column p out kept _ (by omega : 234+j.val<240)] using physical.2.2.2 j

theorem output_distinct (row other column source : Fin 24) (different : column≠source) :
    SchurRow.output row column≠SchurRow.output other source := by
  intro equal
  have same : column=source := by
    apply Fin.ext
    simp only [SchurRow.output] at equal
    omega
  exact different same

theorem executes (columns : List (Fin 24)) (R heap P : ℕ) (p : ℕ→Parts)
    (radius : 3≤R) (physical : BasisColumn.admissible p)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (state : BasisColumn.State R heap P p s) :
    ∃cost t out Q,Executes input tape (code columns) cost s t ∧ BasisColumn.State R heap Q out t ∧
      (∀column∈columns,∀row,(out (SchurRow.output row column)).value=BasisColumn.matrix R p row column) ∧
      (∀i,(i<240 ∨ 384 ≤ i)→i<1200→(∀column∈columns,∀row,i≠SchurRow.output row column)→ out i=p i) ∧
      (∀k,6000≤k→t.val.tapes k=s.val.tapes k) ∧
      (∀k,850≤k→k<924→t.val.tapes k=s.val.tapes k) := by
  induction columns generalizing P p s with
  | nil => exact ⟨1,s,p,P,.skip s,state,by simp,(by intros;rfl),(by intros;rfl),(by intros;rfl)⟩
  | cons column rest ih =>
    obtain ⟨c0,u,next,Pnext,e0,ready0,value0,keep0,high0,interval0⟩:=
      BasisColumn.executes column R heap P p radius physical input tape s state
    obtain ⟨c1,t,out,Q,e1,ready1,value1,keep1,high1,interval1⟩:=
      ih Pnext next (physical_kept column p next keep0 physical) u ready0
    have equalMatrix:=matrix_kept column R p next keep0
    refine ⟨c0+c1,t,out,Q,e0.seq e1,ready1,?_,?_,fun k hk=>(high1 k hk).trans (high0 k hk),
      fun k lo hi=>(interval1 k lo hi).trans (interval0 k lo hi)⟩
    · intro c member row
      rcases List.mem_cons.mp member with equal | later
      · subst c
        by_cases again : column∈rest
        · simpa only [equalMatrix] using value1 column again row
        · rw [keep1 _ (Or.inr (by have b:=SchurRow.output_bounds row column;omega))
            (by have b:=SchurRow.output_bounds row column;omega)]
          · exact value0 row
          · intro other present r
            apply output_distinct
            intro same
            exact again (same ▸ present)
      · simpa only [equalMatrix] using value1 c later row
    · intro i outside low unused
      rw [keep1 i outside low (fun c hc r=>unused c (List.mem_cons_of_mem _ hc) r)]
      exact keep0 i outside low (unused column (by simp))

def fullCode : Code := code (List.finRange 24)

theorem full_executes (R heap P : ℕ) (p : ℕ→Parts) (radius : 3≤R)
    (physical : BasisColumn.admissible p) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (state : BasisColumn.State R heap P p s) :
    ∃cost t out Q,Executes input tape fullCode cost s t ∧ BasisColumn.State R heap Q out t ∧
      (∀row column,(out (SchurRow.output row column)).value=BasisColumn.matrix R p row column) ∧
      (∀i,i<240→ out i=p i) ∧
      (∀k,6000≤k→t.val.tapes k=s.val.tapes k) ∧
      (∀k,850≤k→k<924→t.val.tapes k=s.val.tapes k) := by
  obtain ⟨cost,t,out,Q,execution,output,values,keep,high,interval⟩:=
    executes (List.finRange 24) R heap P p radius physical input tape s state
  refine ⟨cost,t,out,Q,execution,output,fun row column=>values column (by simp) row,?_,high,interval⟩
  intro i low
  apply keep i (Or.inl low) (by omega)
  intro column _ row
  have bounds:=SchurRow.output_bounds row column
  omega

#print axioms full_executes
end Maxwell.Continuum.Calibration.BasisMatrix
