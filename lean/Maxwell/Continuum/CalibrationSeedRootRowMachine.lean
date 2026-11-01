import Maxwell.Continuum.CalibrationSeedRootRowData

/-! The row's cube radius, half-supercell offset and unsigned coordinates
are computed from actual natural words by fixed division/remainder code. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384

def rowCode : Code := .seq (NatAssign.code rowPrepare)
  (.seq (NaturalDivMod.code 750 782 752 784)
    (.seq ArrayDecodeMachine.code (NatAssign.code rowFinish)))
def rowInputWidth (B : ℕ) : ℕ := 2^rowPrepare.length*(B+3)
def rowWidth (B : ℕ) : ℕ := 2*rowInputWidth B+8
def rowCost (B : ℕ) : ℕ := 3000*8^rowPrepare.length*(B+4)^2+
  (2^100*(rowInputWidth B+2)^2+
    (2^110*(rowInputWidth B+5)^2+3000*8^rowFinish.length*(rowWidth B+2)^2))

attribute [local irreducible] ArrayDecodeMachine.code NaturalDivMod.code NatAssign.code

theorem row_executes (v : ℕ→ℕ) (B : ℕ) (width : ∀i∈rowIds,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank rowIds v s.val) (scratch : ∀i,i<5→RationalAccumulator.Blank s.val i) :
    ∃cost t,Executes input tape rowCode cost s t ∧ cost≤rowCost B ∧
      NatAssign.Bank rowIds (rowValues v) t.val ∧
      (∀i,i<5→RationalAccumulator.Blank t.val i) ∧
      (∀i∈rowIds,(rowValues v i).bits.length≤rowWidth B) ∧
      BinaryPrecision.Frame rowWorkspace s.val t.val := by
  have lower (i : ℕ) (hi : i∈rowIds) : 4 ≤ i := (by decide : 4≤10).trans (rowIds_lower i hi)
  have literals : ∀a∈rowPrepare,a.literalWidth≤B+2 := by
    simp [rowPrepare,NatAssign.Instruction.literalWidth,
      show (2:ℕ).bits.length=2 by decide,show (3:ℕ).bits.length=2 by decide]
  obtain ⟨c0,a,e0,h0,ba,za,f0⟩ := NatAssign.executes rowIds lower rowPrepare rowPrepare_valid v
    input tape s bank (fun i hi=>scratch i (by omega))
  change NatAssign.Bank rowIds (rowPrepared v) a.val at ba
  have pwidth : ∀i∈rowIds,(rowPrepared v i).bits.length≤rowInputWidth B := by
    intro i hi
    have hh := NatAssign.values_width rowIds rowPrepare rowPrepare_valid v (B+2)
      (fun i hi=>(width i hi).trans (by omega)) literals i hi
    exact (Nat.le_add_right _ 1).trans hh
  have z4 : RationalAccumulator.Blank a.val 4 := RationalAccumulator.blank_of_eq
    (f0.tapes 4 (by decide)) (scratch 4 (by decide))
  have zs (i : ℕ) (hi : i<5) : RationalAccumulator.Blank a.val i := by
    by_cases hh : i<4
    · exact za i hh
    · have he : i=4 := by omega
      simpa only [he] using z4
  have prepared := rowPrepared_fields v
  obtain ⟨c1,b,e1,h1,bb,zb,f1⟩ := NaturalDivMod.executes rowIds rowIds_lower (by decide)
    750 782 752 784 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (rowPrepared v) prepared.2.2.2.2 (by rw [prepared.2.1];decide) (rowInputWidth B) pwidth input tape a ba zs
  change NatAssign.Bank rowIds (rowHalved v) b.val at bb
  have halfWidth : ∀i∈rowIds,(rowHalved v i).bits.length≤rowInputWidth B :=
    ArrayDecodeMachine.divModValues_width _ rowIds 750 782 752 784 _ (by decide) pwidth
  have positiveWidth : 2≤rowInputWidth B := by change 2≤2048*(B+3);omega
  obtain ⟨c2,c,e2,h2,bc,zc,f2⟩ := ArrayDecodeMachine.executes rowIds rowIds_lower (by decide)
    (by decide) (rowHalved v) (rowHalved_fields v).2.2.2 (rowInputWidth B) positiveWidth
    halfWidth input tape b bb zb
  have decodedWidth : ∀i∈rowIds,(ArrayDecodeMachine.output (rowHalved v) i).bits.length≤rowWidth B :=
    ArrayDecodeMachine.output_width _ rowIds (by decide) _ halfWidth
  obtain ⟨c3,t,e3,h3,bt,zt,f3⟩ := NatAssign.executes rowIds lower rowFinish rowFinish_valid _
    input tape c bc (fun i hi=>zc i (by omega))
  have finalScratch (i : ℕ) (hi : i<5) : RationalAccumulator.Blank t.val i := by
    by_cases hh : i<4
    · exact zt i hh
    · have he : i=4 := by omega
      subst i
      exact RationalAccumulator.blank_of_eq (f3.tapes 4 (by decide)) (zc 4 (by decide))
  have finalWidth : ∀i∈rowIds,(rowValues v i).bits.length≤rowWidth B :=
    NatAssign.values_assignment_width rowIds rowFinish rowFinish_valid _ (rowWidth B) decodedWidth
      (by simp [rowFinish,NatAssign.Instruction.AssignmentBound])
  have price0 := NatAssign.price_bound rowIds rowPrepare rowPrepare_valid v (B+2)
    (fun i hi=>(width i hi).trans (by omega)) literals
  rw [show B+2+2=B+4 by omega] at price0
  have price3 := NatAssign.price_bound rowIds rowFinish rowFinish_valid _ (rowWidth B) decodedWidth
    (by simp [rowFinish,NatAssign.Instruction.literalWidth])
  have widen {xs : List NatAssign.Instruction} (valid : ∀a∈xs,a.Valid rowIds) :
      NatAssign.changes xs⊆rowWorkspace :=
    (NatAssign.changes_subset rowIds xs valid).trans (by decide)
  have execution : Executes input tape rowCode (c0+(c1+(c2+c3))) s t :=
    e0.seq (e1.seq (e2.seq e3))
  have finalBank : NatAssign.Bank rowIds (rowValues v) t.val := bt
  have frame : BinaryPrecision.Frame rowWorkspace s.val t.val :=
    (f0.mono (widen rowPrepare_valid)).trans (f1.trans (f2.trans (f3.mono (widen rowFinish_valid))))
  refine ⟨c0+(c1+(c2+c3)),t,execution,?_,finalBank,finalScratch,finalWidth,frame⟩
  unfold rowCost
  omega

#print axioms row_executes
end Maxwell.Continuum.Calibration.SeedRoot
