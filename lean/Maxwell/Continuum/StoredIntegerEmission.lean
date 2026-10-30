import Maxwell.Continuum.RationalDataflowIntegerEmit
import Maxwell.Continuum.RationalDataflowArrayIndexRead
import Maxwell.Continuum.RationalDataflowArrayFrame
import Maxwell.Continuum.RationalDataflowRowPlan

/-! Emission of a canonical integer already stored in a coefficient table.
The actual indexed reads and bit output are both charged. -/
namespace Maxwell.Continuum.RationalDataflow.StoredInteger
open PartArray Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def slots : Finset ℕ := {0}
def code : Code := .seq (readAtCode 728 0) (IntegerEmit.code 0)

theorem ready_emit_frame {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (h : Ready S v s) (f : EmitNatural.Frame s t) : Ready S v t := by
  exact ⟨fun i hi => RationalAccumulator.word_of_eq (congrFun f.2.2.2.2 i) (h.1 i hi),
    fun i hi => RationalAccumulator.blank_of_eq (congrFun f.2.2.2.2 i) (h.2 i hi)⟩

theorem table_emit_frame {n : ℕ} {a : Table n} {s t : Store}
    (h : a.Ready s) (f : EmitNatural.Frame s t) : a.Ready t := by
  have same (i : ℕ) := congrFun f.2.2.2.2 i
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact RationalAccumulator.blank_of_eq (same 0) h.scratch.1
  · exact RationalAccumulator.blank_of_eq (same 1) h.scratch.2.1
  · exact RationalAccumulator.blank_of_eq (same 2) h.scratch.2.2.1
  · exact RationalAccumulator.blank_of_eq (same 3) h.scratch.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (same 5) h.scratch.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (same 6) h.scratch.2.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (same 8) h.scratch.2.2.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (same 9) h.scratch.2.2.2.2.2.2.2
  · exact RationalAccumulator.blank_of_eq (same 7) h.seven
  · exact BankArray.word_of_eq (same 200) h.width
  · exact BankArray.word_of_eq (same 202) h.basePositive
  · exact BankArray.word_of_eq (same 203) h.baseNegative
  · exact BankArray.word_of_eq (same 204) h.baseDenominator
  · exact BankArray.word_of_eq (same 205) h.clock
  · simpa only [f.2.2.1] using h.positive
  · simpa only [f.2.2.1] using h.negative
  · simpa only [f.2.2.1] using h.denominator

theorem canonical_abs_width (z : ℤ) (B : ℕ) (h : (Parts.literal (z:ℚ)).Width B) :
    z.natAbs.bits.length≤B := by
  by_cases hz : 0≤z
  · have he : z.natAbs=z.toNat := by omega
    simpa [he,Parts.literal] using h.1
  · have he : z.natAbs=(-z).toNat := by omega
    simpa [he,Parts.literal] using h.2.1

theorem executes {n : ℕ} (a : Table n) (z : ℕ→ℤ)
    (hc : ∀i:Fin n,a.get i=Parts.literal ((z i.val:ℤ):ℚ))
    (B : ℕ) (hm : a.MetadataWidth B) (i : Fin n) (hi : i.val.bits.length≤B)
    (v : ℕ→Parts) (hv : WidthBank slots B v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready slots v s) (ha : a.Ready s)
    (hindex : RationalAccumulator.Word s.val 728 i.val) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤2^22*(B+5)^2 ∧
      Ready slots (Function.update v 0 (a.get i)) t ∧ a.Ready t ∧
      WidthBank slots B (Function.update v 0 (a.get i)) ∧
      t.val.output=(Codec.int (z i.val)).reverse++s.val.output ∧
      t.val.memory=s.val.memory ∧
      (∀k,10 ≤ k → k∉cellPorts 0 → t.val.tapes k=s.val.tapes k) := by
  obtain ⟨c0,s0,e0,hc0,r0,a0,_,f0⟩ := readAt_executes a slots 728 0 (by decide) (by decide)
    (by decide) v input tape i.val.bits i (addressValue_bits _) s hr ha hindex
  have hwidth := a.get_width B hm s ha i
  have hp : RationalAccumulator.Word s0.val (positivePort 0) (z i.val).toNat := by
    have h := r0.1 (positivePort 0) (cell_mem (by decide : 0∈slots) (by simp [cellPorts]))
    simpa [dataValues_positive,Function.update_self,hc i,Parts.literal] using h
  have hn : RationalAccumulator.Word s0.val (negativePort 0) (-(z i.val)).toNat := by
    have h := r0.1 (negativePort 0) (cell_mem (by decide : 0∈slots) (by simp [cellPorts]))
    simpa [dataValues_negative,Function.update_self,hc i,Parts.literal] using h
  obtain ⟨t,e1,out,frame⟩ := IntegerEmit.executes 0 (z i.val) input tape s0 hp hn
  have costread := a.readCost_bound B hm i.val.bits hi (v 0) (hv 0 (by decide))
  have costout := canonical_abs_width (z i.val) B (by simpa only [hc i] using hwidth)
  refine ⟨c0+(20*(z i.val).natAbs.bits.length+30),t,e0.seq e1,?_,
    ready_emit_frame r0 frame,table_emit_frame a0 frame,hv.update 0 hwidth,?_,?_,?_⟩
  · nlinarith only [hc0,costread,costout,Nat.zero_le B]
  · simpa only [f0.output] using out
  · exact frame.2.2.1.trans f0.memory
  · intro k hk hkp
    exact (congrFun frame.2.2.2.2 k).trans (f0.tapes k hk hkp)

#print axioms executes
end Maxwell.Continuum.RationalDataflow.StoredInteger
