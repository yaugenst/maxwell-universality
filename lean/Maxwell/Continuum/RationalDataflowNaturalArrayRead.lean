import Maxwell.Continuum.RationalDataflowArray
import Maxwell.Continuum.RationalDataflowNaturalChannels

/-! A literal fixed-width source array can feed the positive channel of
a shared rational register. Addressing, old-word cleanup and canonical
binary normalization are all executed by the existing array reader. -/
namespace Maxwell.Continuum.RationalDataflow.NaturalArrayRead
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def code (width index base clock target : ℕ) : Code :=
  ArrayRead.code width index base clock (positivePort target)

def values (v : ℕ→Parts) (target n : ℕ) : ℕ→Parts :=
  Function.update v target (NaturalChannel.replace .positive (v target) n)

theorem executes {n : ℕ} (S : Finset ℕ) (target widthBank indexBank baseBank clockBank : ℕ)
    (ht : target∈S) (hwb : 10≤widthBank ∧ widthBank<1000)
    (hib : 10 ≤ indexBank ∧ indexBank<1000) (hbb : 10≤baseBank ∧ baseBank<1000)
    (hcb : 10≤clockBank ∧ clockBank<1000)
    (width index base clock : List Bool) (a : Vector (List Bool) n) (i : Fin n)
    (hwidth : 0<width.length) (hindex : addressValue index=i.val)
    (hclock : clock.length=addressValue width)
    (v : ℕ→Parts) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready S v s) (hs : BankArray.Scratch s.val) (h7 : RationalAccumulator.Blank s.val 7)
    (ww : BankArray.Word s.val widthBank width) (wi : BankArray.Word s.val indexBank index)
    (wb : BankArray.Word s.val baseBank base) (wc : BankArray.Word s.val clockBank clock)
    (ha : BitArray.Represents s.val.memory (addressValue base) (addressValue width) a) :
    ∃cost t,Executes input tape (code widthBank indexBank baseBank clockBank target) cost s t ∧
      cost≤6*(v target).positive.bits.length+BankArray.costCap width index base clock+
        32*addressValue width+46 ∧
      Ready S (values v target (addressValue (a.get i))) t ∧
      BankArray.Scratch t.val ∧ RationalAccumulator.Blank t.val 7 ∧
      ArrayRead.Frame (positivePort target) s.val t.val := by
  have hp := positivePort_ge target
  obtain ⟨cost,t,ex,hc,hb,hz,hseven,_,hf⟩ := ArrayRead.executes (ids S) (ids_ge_ten S)
    widthBank indexBank baseBank clockBank (positivePort target)
    hwb.1 hib.1 hbb.1 hcb.1 (cell_mem ht (by simp [cellPorts]))
    (by omega) (by omega) (by omega) (by omega) input tape width index base clock a i
    hwidth hindex hclock (dataValues v) s hr.1 hs h7 ww wi wb wc ha
  have he := NaturalChannel.replace_dataValues .positive v target (addressValue (a.get i))
  change Function.update (dataValues v) (positivePort target) (addressValue (a.get i)) = _ at he
  rw [he] at hb
  refine ⟨cost,t,ex,?_,⟨hb,?_⟩,hz,hseven,hf⟩
  · simpa only [dataValues_positive] using hc
  · intro k hk
    interval_cases k
    · exact hz.1
    · exact hz.2.1
    · exact hz.2.2.1
    · exact hz.2.2.2.1

theorem values_valid {S : Finset ℕ} {v : ℕ→Parts} (hg : Good S v) (target n : ℕ) :
    Good S (values v target n) := by
  intro i hi
  by_cases he : i=target
  · subst i
    simpa only [values,Function.update_self,NaturalChannel.replace,Parts.Valid] using hg target hi
  · simpa only [values,Function.update_of_ne he] using hg i hi

#print axioms executes
end Maxwell.Continuum.RationalDataflow.NaturalArrayRead
