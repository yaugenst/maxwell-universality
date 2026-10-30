import Maxwell.Continuum.FourierTensorModeFrames
import Maxwell.Continuum.RationalDataflowRowPlan

/-! The two calibrated amplitude coordinates are read at the actually
computed indices, including the runtime imaginary-block offset. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeIndex
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def readCode : Code := .seq (readAtCode 310 2) (readAtCode 321 3)
def readValues (R : ℕ) (a : Table (2*aliasArraySize R)) (j : Fin 3)
    (r : Fin (RowArithmetic.rowCount R)) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update (Function.update v
    2 (a.get (GlobalPower.realIndex R (0,RowArithmetic.rowIndex R j r))))
    3 (a.get (GlobalPower.realIndex R (1,RowArithmetic.rowIndex R j r)))

theorem realIndex_value (R : ℕ) (i : Fin (aliasArraySize R)) :
    (GlobalPower.realIndex R (0,i)).val=i.val := by simp [GlobalPower.realIndex,finProdFinEquiv]
theorem imagIndex_value (R : ℕ) (i : Fin (aliasArraySize R)) :
    (GlobalPower.realIndex R (1,i)).val=aliasArraySize R+i.val := by
  simp [GlobalPower.realIndex,finProdFinEquiv,Nat.add_comm]

theorem read_bank_frame {target : ℕ} {n : ℕ→ℕ} {s t : Store}
    (h : NatAssign.Bank ports n s.val) (f : PartArray.Frame target s.val t.val) :
    NatAssign.Bank ports n t.val := by
  intro i hi
  have hb : 10 ≤ i ∧ i<1000 := by simp only [ports,Finset.mem_Icc] at hi;omega
  exact RationalAccumulator.word_of_eq (read_tapes f i hb.1 hb.2) (h i hi)

theorem read_to_plan {target : ℕ} {s t : BitRAMState} (f : PartArray.Frame target s t)
    (ht : target∈RowArithmetic.bank) : RowPlanFrame RowArithmetic.bank s t := by
  refine ⟨f.memory,f.inputHead,f.randomCursor,f.output,?_⟩
  intro i hi hp _
  apply f.tapes i hi
  intro hh
  exact hp (Finset.mem_biUnion.mpr ⟨target,ht,hh⟩)

theorem read_executes (R W : ℕ) (a : Table (2*aliasArraySize R))
    (j : Fin 3) (r : Fin (RowArithmetic.rowCount R)) (v : ℕ→Parts)
    (hma : a.MetadataWidth W) (hw : WidthBank RowArithmetic.bank W v)
    (hg : Good RowArithmetic.bank v) (haValid : ∀i,(a.get i).Valid)
    (hnat : ∀i∈ports,(values j R (aliasArraySize R) r.val i).bits.length≤64*(W+1))
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : RationalDataflow.Ready RowArithmetic.bank v s) (ha : a.Ready s)
    (hb : NatAssign.Bank ports (values j R (aliasArraySize R) r.val) s.val)
    (hclean : DyadicFloor.Clean s.val) :
    ∃cost t,Executes input tape readCode cost s t ∧ cost≤2^40*(W+5)^2 ∧
      RationalDataflow.Ready RowArithmetic.bank (readValues R a j r v) t ∧
      WidthBank RowArithmetic.bank W (readValues R a j r v) ∧
      Good RowArithmetic.bank (readValues R a j r v) ∧ a.Ready t ∧
      NatAssign.Bank ports (values j R (aliasArraySize R) r.val) t.val ∧
      DyadicFloor.Clean t.val ∧ RowPlanFrame RowArithmetic.bank s.val t.val := by
  let n := values j R (aliasArraySize R) r.val
  let i0 := GlobalPower.realIndex R (0,RowArithmetic.rowIndex R j r)
  let i1 := GlobalPower.realIndex R (1,RowArithmetic.rowIndex R j r)
  have hi0 : addressValue (n 310).bits=i0.val := by
    simp only [n,i0,addressValue_bits,values_real,realIndex_value,RowArithmetic.rowIndex_value]
  have hi1 : addressValue (n 321).bits=i1.val := by
    simp only [n,i1,addressValue_bits,values_imag,imagIndex_value,RowArithmetic.rowIndex_value]
  obtain ⟨c0,s0,e0,hc0,b0,a0,_,f0⟩ := readAt_executes a RowArithmetic.bank 310 2
    (by decide) (by decide) (by decide) v input tape (n 310).bits i0 hi0 s hs ha
    (hb 310 (by simp [ports]))
  let v0 := Function.update v 2 (a.get i0)
  have w0 : WidthBank RowArithmetic.bank W v0 := hw.update 2 (a.get_width W hma s ha i0)
  have g0 : Good RowArithmetic.bank v0 := hg.update 2 (haValid i0)
  have bn0 := read_bank_frame hb f0
  have z0 := read_floor_frame hclean f0 (e0.protectsTape 4 (by decide))
  obtain ⟨c1,t,e1,hc1,b1,a1,_,f1⟩ := readAt_executes a RowArithmetic.bank 321 3
    (by decide) (by decide) (by decide) v0 input tape (n 321).bits i1 hi1 s0 b0 a0
    (bn0 321 (by simp [ports]))
  have w1 := w0.update 3 (a.get_width W hma s ha i1)
  have g1 := g0.update 3 (haValid i1)
  refine ⟨c0+c1,t,e0.seq e1,?_,b1,w1,g1,a1,read_bank_frame bn0 f1,
    read_floor_frame z0 f1 (e1.protectsTape 4 (by decide)),
    (read_to_plan f0 (by decide)).trans (read_to_plan f1 (by decide))⟩
  have hW : W≤64*(W+1) := by omega
  have h0 := hc0.trans (a.readCost_bound (64*(W+1)) (hma.mono hW) _
    (hnat 310 (by simp [ports])) _ ((hw 2 (by decide)).mono hW))
  have h1 := hc1.trans (a.readCost_bound (64*(W+1)) (hma.mono hW) _
    (hnat 321 (by simp [ports])) _ ((w0 3 (by decide)).mono hW))
  nlinarith only [h0,h1,Nat.zero_le W]

#print axioms read_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeIndex
