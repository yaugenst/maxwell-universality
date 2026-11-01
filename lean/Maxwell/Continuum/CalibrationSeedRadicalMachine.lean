import Maxwell.Continuum.RationalSquareRootOutputBank
import Maxwell.Continuum.RationalSquareRootRaw
import Maxwell.Continuum.CalibrationSeedScalars
import Maxwell.Cost.Structured.NatAssign.BankFrame

/-! The first seed scalar is computed by the actual integer-root program
at precision N+7, with charged reset of its previously stored workspace. -/
namespace Maxwell.Continuum.Calibration.SeedMachine
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 12000

def savedIds : Finset ℕ := Finset.Icc 700 749
def ids : Finset ℕ := RationalRoot.Raw.ids∪savedIds
def workspace : Finset ℕ := {0,1,2,3}∪ids
def rootClear : List ℕ := (List.range 549).filter (fun i=>i∈RationalRoot.ids\{542,543,544})
def radicalPrepare : List NatAssign.Instruction :=
  [.copy 700 544,.literal 701 7,.add 701 544,.literal 542 19,.literal 543 1]++
    rootClear.map (fun i=>.literal i 0)
def radicalPrepared (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values radicalPrepare v
def radicalValues (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.overlay RationalRoot.ids
  (RationalRoot.outputValues 19 1 (v 700+7)) (radicalPrepared v)
def radicalCode : Code := .seq (NatAssign.code radicalPrepare) RationalRoot.code
def radicalInputWidth (B : ℕ) : ℕ := 2^radicalPrepare.length*(B+6)
def radicalWidth (N B : ℕ) : ℕ := max (radicalInputWidth B)
  (RationalRoot.outputWidth (N+7) (radicalInputWidth B))
def radicalCost (N B : ℕ) : ℕ := 3000*8^radicalPrepare.length*(B+7)^2+
  RationalRoot.costBound (N+7) (radicalInputWidth B)

theorem ids_ge : ∀i∈ids,4 ≤ i := by
  intro i hi
  rcases Finset.mem_union.mp hi with hr|hs
  · exact RationalRoot.Raw.ids_ge i hr
  · have :=(Finset.mem_Icc.mp hs).1;omega
theorem rootClear_mem (i : ℕ) : i∈rootClear ↔ i∈RationalRoot.ids\{542,543,544} := by
  have bound : ∀j∈RationalRoot.ids,j<549 := by decide+kernel
  simp only [rootClear,List.mem_filter,List.mem_range,decide_eq_true_eq]
  exact ⟨And.right,fun h=>⟨bound i (Finset.mem_sdiff.mp h).1,h⟩⟩
theorem radicalPrepare_valid : ∀a∈radicalPrepare,a.Valid ids := by
  intro a ha
  simp only [radicalPrepare,List.mem_append] at ha
  rcases ha with first|rest
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at first
    rcases first with rfl|rfl|rfl|rfl|rfl <;>
      simp [NatAssign.Instruction.Valid,ids,savedIds,RationalRoot.Raw.ids,RationalRoot.ids]
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp rest
    have member : i∈RationalRoot.ids\{542,543,544} := by
      exact (rootClear_mem i).mp hi
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_sdiff.mp member).1)

theorem radicalPrepared_root (v : ℕ→ℕ) (i : ℕ) (hi : i∈RationalRoot.ids) :
    radicalPrepared v i=RationalRoot.inputValues 19 1 (v 700+7) i := by
  simp only [radicalPrepared,radicalPrepare,NatAssign.values_append,NatAssign.values_literals,
    rootClear_mem,Finset.mem_sdiff]
  by_cases a : i=542
  · subst i;simp [NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,RationalRoot.inputValues]
  by_cases b : i=543
  · subst i;simp [NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,RationalRoot.inputValues]
  by_cases c : i=544
  · subst i;simp [NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,RationalRoot.inputValues,Nat.add_comm]
  simp [hi,a,b,c,RationalRoot.inputValues]

theorem radicalValue (N : ℕ) :
    (Nat.sqrt (RationalRoot.radicand 19 1 (N+7)):ℚ)/(2^(N+7):ℕ)=seedRadical N := by
  have h := RationalRoot.literal_value (19:ℚ) (N+7)
  simpa only [show (19:ℚ).num.natAbs=19 by decide,show (19:ℚ).den=1 by decide,
    Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat,one_mul,sqrtRationalCenter,div_one,seedRadical,mul_one] using h

theorem radicalValues_fields (v : ℕ→ℕ) :
    radicalValues v 32=Nat.sqrt (RationalRoot.radicand 19 1 (v 700+7)) ∧
    radicalValues v 548=2^(v 700+7) ∧ radicalValues v 544=v 700+7 ∧ radicalValues v 700=v 700 := by
  refine ⟨?_,?_,?_,?_⟩
  · simp [radicalValues,NatAssign.overlay,RationalRoot.outputValues,RationalRoot.ids,
      NaturalRoot.fullIds,NaturalRoot.ids,NaturalRoot.doneValues,DyadicSqrt.bank]
  · simp [radicalValues,NatAssign.overlay,RationalRoot.outputValues,RationalRoot.ids,
      NaturalRoot.fullIds,NaturalRoot.ids]
  · simp [radicalValues,NatAssign.overlay,RationalRoot.outputValues,RationalRoot.ids,
      NaturalRoot.fullIds,NaturalRoot.ids,RationalRoot.inputValues]
  · rw [radicalValues,NatAssign.overlay_outside _ _ _ (by decide)]
    exact NatAssign.values_preserves radicalPrepare v 700 (by decide+kernel)

theorem radical_executes (v : ℕ→ℕ) (B : ℕ) (width : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape radicalCode cost s t ∧ cost≤radicalCost (v 700) B ∧
      NatAssign.Bank ids (radicalValues v) t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈ids,(radicalValues v i).bits.length≤radicalWidth (v 700) B) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  have literals : ∀a∈radicalPrepare,a.literalWidth≤B+5 := by
    intro a ha
    simp only [radicalPrepare,List.mem_append] at ha
    rcases ha with first|rest
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at first
      rcases first with rfl|rfl|rfl|rfl|rfl <;>
        simp [NatAssign.Instruction.literalWidth,
          show (7:ℕ).bits.length=3 by decide,show (19:ℕ).bits.length=5 by decide]
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp rest
      simp [NatAssign.Instruction.literalWidth]
  obtain ⟨c0,a,e0,h0,ba,sa,f0⟩ := NatAssign.executes ids ids_ge radicalPrepare radicalPrepare_valid
    v input tape s bank scratch
  change NatAssign.Bank ids (radicalPrepared v) a.val at ba
  have wa : ∀i∈ids,(radicalPrepared v i).bits.length≤radicalInputWidth B := by
    intro i hi
    have h := NatAssign.values_width ids radicalPrepare radicalPrepare_valid v (B+5)
      (fun i hi=>(width i hi).trans (by omega)) literals i hi
    exact (Nat.le_add_right _ 1).trans h
  have rootBank : NatAssign.Bank RationalRoot.ids (RationalRoot.inputValues 19 1 (v 700+7)) a.val := by
    intro i hi
    simpa only [radicalPrepared_root v i hi] using ba i (Finset.mem_union_left _ (Finset.mem_union_left _ hi))
  have wr (i : ℕ) (hi : i∈RationalRoot.ids) :
      (RationalRoot.inputValues 19 1 (v 700+7) i).bits.length≤radicalInputWidth B := by
    rw [←radicalPrepared_root v i hi]
    exact wa i (Finset.mem_union_left _ (Finset.mem_union_left _ hi))
  obtain ⟨c1,t,e1,h1,bt,st,f1⟩ := RationalRoot.executes_bank 19 1 (v 700+7) (radicalInputWidth B)
    (by simpa [RationalRoot.inputValues] using wr 542 (by decide))
    (by simpa [RationalRoot.inputValues] using wr 543 (by decide))
    (by simpa [RationalRoot.inputValues] using wr 544 (by decide)) input tape a rootBank sa
  have framed : BinaryPrecision.Frame (RationalRoot.ids∪{0,1,2,3}) a.val t.val :=
    f1.mono (by decide+kernel)
  have fullBank := NatAssign.Bank.overlay ba bt (by
    apply Finset.disjoint_left.mpr
    intro i hi small
    have := ids_ge i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at small
    omega) framed
  have fullWidth := NatAssign.overlay_width (owned := RationalRoot.ids) wa (fun i _=>RationalRoot.output_width 19 1 (v 700+7)
    (radicalInputWidth B)
    (by simpa [RationalRoot.inputValues] using wr 542 (by decide))
    (by simpa [RationalRoot.inputValues] using wr 543 (by decide))
    (by simpa [RationalRoot.inputValues] using wr 544 (by decide)) i)
  have price := NatAssign.price_bound ids radicalPrepare radicalPrepare_valid v (B+5)
    (fun i hi=>(width i hi).trans (by omega)) literals
  refine ⟨c0+c1,t,e0.seq e1,Nat.add_le_add (h0.trans price) h1,fullBank,st,fullWidth,?_⟩
  exact (f0.mono (NatAssign.changes_subset ids radicalPrepare radicalPrepare_valid)).trans
    (f1.mono (by decide+kernel))

#print axioms radical_executes
end Maxwell.Continuum.Calibration.SeedMachine
