import Maxwell.Continuum.FourierTensorGeneratedCoefficient
import Maxwell.Continuum.RationalDataflowIntegerEmit

/-! Output emission leaves every represented Fourier/wave bank ready for
the next tensor coefficient. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator

theorem Ready.same_tapes {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (h : Ready S v s) (ht : t.val.tapes=s.val.tapes) : Ready S v t :=
  ⟨fun i hi => word_of_eq (congrFun ht i) (h.1 i hi),
    fun i hi => blank_of_eq (congrFun ht i) (h.2 i hi)⟩

namespace PartArray

theorem Table.Ready.same_memory_tapes {n : ℕ} {a : Table n} {s t : Store}
    (h : a.Ready s) (hm : t.val.memory=s.val.memory) (ht : t.val.tapes=s.val.tapes) : a.Ready t := by
  have hz : BankArray.Scratch t.val := by
    rcases h.scratch with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
    exact ⟨blank_of_eq (congrFun ht 0) h0,blank_of_eq (congrFun ht 1) h1,
      blank_of_eq (congrFun ht 2) h2,blank_of_eq (congrFun ht 3) h3,
      blank_of_eq (congrFun ht 5) h5,blank_of_eq (congrFun ht 6) h6,
      blank_of_eq (congrFun ht 8) h8,blank_of_eq (congrFun ht 9) h9⟩
  exact ⟨hz,blank_of_eq (congrFun ht 7) h.seven,
    BankArray.word_of_eq (congrFun ht 200) h.width,
    BankArray.word_of_eq (congrFun ht 202) h.basePositive,
    BankArray.word_of_eq (congrFun ht 203) h.baseNegative,
    BankArray.word_of_eq (congrFun ht 204) h.baseDenominator,
    BankArray.word_of_eq (congrFun ht 205) h.clock,
    by simpa only [hm] using h.positive,
    by simpa only [hm] using h.negative,
    by simpa only [hm] using h.denominator⟩

end PartArray
end Maxwell.Continuum.RationalDataflow

namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
open RationalDataflow.PartArray
set_option maxHeartbeats 2500000

theorem FactorReady.same_memory_tapes {n D Q N : ℕ} {a : Table n} {b : Table (2*D)}
    {v : ℕ→Parts} {s t : Store} (h : FactorReady a Q N b v s)
    (hm : t.val.memory=s.val.memory) (ht : t.val.tapes=s.val.tapes) : FactorReady a Q N b v t := by
  have source := h.source.same_memory_tapes hm ht
  refine ⟨h.ready.same_tapes ht,?_,?_,?_,source,?_,
    blank_of_eq (congrFun ht 144) h.power,blank_of_eq (congrFun ht 146) h.powerCount,
    blank_of_eq (congrFun ht 680) h.inner,?_⟩
  · exact fun i hi => blank_of_eq (congrFun ht i) (h.phase i hi)
  · exact ⟨blank_of_eq (congrFun ht 4) h.floor.1,
      fun i hi => blank_of_eq (congrFun ht i) (h.floor.2 i hi)⟩
  · exact fun i hi => word_of_eq (congrFun ht i) (h.setup i hi)
  · exact h.output.transfer hm (fun i _ => congrFun ht i) source.scratch source.seven
  · exact fun i hi => blank_of_eq (congrFun ht i) (h.saved i hi)

theorem emitCoefficient_executes {n D Q N : ℕ} {a : Table n} {b : Table (2*D)}
    (v : ℕ→Parts) (z : ℤ) (hz : v 32=Parts.literal (z:ℚ))
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : FactorReady a Q N b v s)
    (hr : Ready termBank v s) :
    ∃t,Executes input tape (IntegerEmit.code 32) (20*z.natAbs.bits.length+30) s t ∧
      t.val.output=(Codec.int z).reverse++s.val.output ∧
      FactorReady a Q N b v t ∧ Ready termBank v t ∧ t.val.tapes=s.val.tapes := by
  have hp : Word s.val (positivePort 32) z.toNat := by
    have h := hr.1 (positivePort 32) (cell_mem (i := 32) (by simp [termBank]) (by simp [cellPorts]))
    simpa only [dataValues_positive,hz,Parts.literal,Rat.num_intCast] using h
  have hn : Word s.val (negativePort 32) (-z).toNat := by
    have h := hr.1 (negativePort 32) (cell_mem (i := 32) (by simp [termBank]) (by simp [cellPorts]))
    simpa only [dataValues_negative,hz,Parts.literal,Rat.num_intCast] using h
  obtain ⟨t,he,ho,hf⟩ := IntegerEmit.executes 32 z input tape s hp hn
  exact ⟨t,he,ho,hs.same_memory_tapes hf.2.2.1 hf.2.2.2.2,
    hr.same_tapes hf.2.2.2.2,hf.2.2.2.2⟩

#print axioms emitCoefficient_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
