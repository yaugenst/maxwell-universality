import Maxwell.Continuum.RationalDataflowTrace
import Maxwell.Cost.NormalizedRecordParser.ShiftedRational
import Maxwell.Cost.Structured.NatAssign.Values

/-! A parsed source rational is deposited into the ordinary raw rational
register by charged copies selected by the actual parsed sign bit. -/
namespace Maxwell.Continuum.SourcePayload
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def loadIds : Finset ℕ:={4801,4802,1000,1001,1002}
def loadPlan (negative : Bool):List NatAssign.Instruction:=
  if negative then [.literal 1000 0,.copy 4801 1001,.copy 4802 1002]
  else [.literal 1001 0,.copy 4801 1000,.copy 4802 1002]
def loadCode : Code:=.branch 23 (NatAssign.code (loadPlan true)) (NatAssign.code (loadPlan false))
def loadValues (q : ℚ) (v : ℕ→Parts) (i : ℕ):=
  if i=4801 then q.num.natAbs else if i=4802 then q.den else dataValues v i

theorem load_valid (negative : Bool):∀a∈loadPlan negative,a.Valid loadIds:=by
  cases negative <;> simp [loadPlan,loadIds,NatAssign.Instruction.Valid]

theorem load_result (q : ℚ) (v : ℕ→Parts):
    NatAssign.values (loadPlan (decide (q.num<0))) (loadValues q v) 1000=q.num.toNat ∧
    NatAssign.values (loadPlan (decide (q.num<0))) (loadValues q v) 1001=(-q.num).toNat ∧
    NatAssign.values (loadPlan (decide (q.num<0))) (loadValues q v) 1002=q.den:=by
  by_cases negative : q.num<0
  all_goals simp [loadPlan,negative,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,loadValues]
  all_goals omega

theorem load_executes (S : Finset ℕ) (h0 : 0∈S) (q : ℚ) (v : ℕ→Parts) (B : ℕ)
    (hv : WidthBank S B v) (hn : q.num.natAbs.bits.length≤B) (hd : q.den.bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (ready : RationalDataflow.Ready S v s)
    (numerator : Word s.val 4801 q.num.natAbs) (denominator : Word s.val 4802 q.den)
    (sign : s.val.registers 23=decide (q.num<0)):
    ∃cost t,Executes input tape loadCode cost s t ∧cost≤2^23*(B+2)^2 ∧
      RationalDataflow.Ready S (Function.update v 0 (Parts.literal q)) t ∧
      WidthBank S B (Function.update v 0 (Parts.literal q)) ∧
      BinaryPrecision.Frame {0,1,2,3,1000,1001,1002} s.val t.val:=by
  have lower : ∀i∈loadIds,4 ≤ i:=by simp only [loadIds,Finset.mem_insert,Finset.mem_singleton];omega
  have initial : NatAssign.Bank loadIds (loadValues q v) s.val:=by
    intro i hi
    simp only [loadIds,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl
    · simpa [loadValues] using numerator
    · simpa [loadValues] using denominator
    all_goals simpa [loadValues] using ready.1 _ (cell_mem h0 (by decide))
  have widths : ∀i∈loadIds,(loadValues q v i).bits.length≤B:=by
    intro i hi
    simp only [loadIds,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl
    · simpa [loadValues] using hn
    · simpa [loadValues] using hd
    all_goals simpa [loadValues] using dataValues_width S v B hv _ (cell_mem h0 (by decide))
  have literalWidths (negative : Bool):∀a∈loadPlan negative,a.literalWidth≤B:=by
    cases negative <;> simp [loadPlan,NatAssign.Instruction.literalWidth]
  obtain ⟨c,t,ex,hc,bank,zero,frame⟩:=NatAssign.executes loadIds lower (loadPlan (decide (q.num<0)))
    (load_valid _) (loadValues q v) input tape s initial ready.2
  have run : Executes input tape loadCode (1+c) s t:=by
    cases he : decide (q.num<0) with
    | false => exact Executes.no (sign.trans he) (by simpa only [he] using ex)
    | true => exact Executes.yes (sign.trans he) (by simpa only [he] using ex)
  have frame' : BinaryPrecision.Frame {0,1,2,3,1000,1001,1002} s.val t.val:=frame.mono (by
    cases he : decide (q.num<0) <;> simp [loadPlan,NatAssign.changes,NatAssign.Instruction.target,Finset.subset_iff])
  have partsWidth : (Parts.literal q).Width B:=by
    have hp : q.num.toNat≤q.num.natAbs:=by omega
    have hm : (-q.num).toNat≤q.num.natAbs:=by omega
    have hp' : q.num.toNat.bits.length≤q.num.natAbs.bits.length:=by
      simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hp
    have hm' : (-q.num).toNat.bits.length≤q.num.natAbs.bits.length:=by
      simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hm
    exact ⟨hp'.trans hn,hm'.trans hn,hd⟩
  refine ⟨1+c,t,run,?_,⟨?_,zero⟩,hv.update 0 partsWidth,frame'⟩
  · have hp:=NatAssign.price_bound loadIds (loadPlan (decide (q.num<0))) (load_valid _)
      (loadValues q v) B widths (literalWidths _)
    have length : (loadPlan (decide (q.num<0))).length=3:=by cases he : decide (q.num<0) <;> rfl
    rw [length] at hp
    nlinarith only [hc,hp,Nat.zero_le B]
  · intro i hi
    by_cases cell : i∈cellPorts 0
    · simp only [cellPorts,positivePort,negativePort,denominatorPort,Finset.mem_insert,Finset.mem_singleton] at cell
      rcases cell with rfl|rfl|rfl
      · have hb:=bank 1000 (by decide)
        rw [(load_result q v).1] at hb
        simpa [dataValues,Parts.literal] using hb
      · have hb:=bank 1001 (by decide)
        rw [(load_result q v).2.1] at hb
        simpa [dataValues,Parts.literal] using hb
      · have hb:=bank 1002 (by decide)
        rw [(load_result q v).2.2] at hb
        simpa [dataValues,Parts.literal] using hb
    · have keep : i∉({0,1,2,3,1000,1001,1002}:Finset ℕ):=by
        have lower:=RationalDataflow.ids_ge S i hi
        simpa only [cellPorts,positivePort,negativePort,denominatorPort,Finset.mem_insert,Finset.mem_singleton,not_or] using
          (show i≠0 ∧i≠1 ∧i≠2 ∧i≠3 ∧i≠1000 ∧i≠1001 ∧i≠1002 by
            simp only [cellPorts,positivePort,negativePort,denominatorPort,Finset.mem_insert,Finset.mem_singleton,not_or] at cell
            omega)
      have old:=word_of_eq (frame'.tapes i keep) (ready.1 i hi)
      rw [←writeParts_dataValues]
      simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton,not_or] at cell
      simpa only [writeParts,Function.update_of_ne cell.1,
        Function.update_of_ne cell.2.1,Function.update_of_ne cell.2.2] using old


#print axioms load_executes
end Maxwell.Continuum.SourcePayload
