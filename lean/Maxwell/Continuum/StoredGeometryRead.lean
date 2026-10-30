import Maxwell.Continuum.StoredGeometryLayout
import Maxwell.Cost.IncidencePass.Common

/-! The geometry cursor performs an actual indexed natural read, including
clearing the previous result and trimming its stored fixed-width word. -/
namespace Maxwell.Continuum.GeometryOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def readCode (target : ℕ) : Code := RationalDataflow.ArrayRead.code 961 971 960 962 target

theorem read_executes {n : ℕ} (values : Vector ℕ n) (base width B : ℕ) (clock : List Bool)
    (hwidth : 0<width) (hwidthB : width≤B) (hlen : clock.length=width)
    (target : ℕ) (ht : target∈ids) (ht₀ : target≠960) (ht₁ : target≠961) (ht₂ : target≠962)
    (hti : target≠971) (v : ℕ→ℕ) (hv : ∀i∈ids,(v i).bits.length≤B)
    (hbase : v 960=base) (hwidthv : v 961=width) (i : Fin n) (hindex : v 971=i.val)
    (hfit : (values.get i).bits.length≤width)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready v s)
    (hclock : BankArray.Word s.val 962 clock)
    (harray : BitArray.Represents s.val.memory base width (IncidenceEncoding.words width values)) :
    ∃cost t,Executes input tape (readCode target) cost s t ∧ cost≤2^20*(B+3)^2 ∧
      Ready (Function.update v target (values.get i)) t ∧
      BitArray.Represents t.val.memory base width (IncidenceEncoding.words width values) ∧
      BankArray.Word t.val 962 clock ∧ RationalDataflow.ArrayRead.Frame target s.val t.val := by
  have hvWidth : BankArray.Word s.val 961 width.bits := by
    simpa only [hwidthv,RationalAccumulator.Word,BankArray.Word] using hs.bank 961 (by decide)
  have hvBase : BankArray.Word s.val 960 base.bits := by
    simpa only [hbase,RationalAccumulator.Word,BankArray.Word] using hs.bank 960 (by decide)
  have hvIndex : BankArray.Word s.val 971 i.val.bits := by
    simpa only [hindex,RationalAccumulator.Word,BankArray.Word] using hs.bank 971 (by decide)
  obtain ⟨cost,t,ex,hc,hb,hz,h7,ha,hf⟩ := RationalDataflow.ArrayRead.executes ids
    (fun k hk => (by omega : 10≤960).trans (ids_ge k hk)) 961 971 960 962 target
    (by decide) (by decide) (by decide) (by decide) ht ht₁.symm hti.symm ht₀.symm ht₂.symm
    input tape width.bits i.val.bits base.bits clock (IncidenceEncoding.words width values) i
    (bits_nonempty hwidth) (addressValue_bits _) (by simpa only [addressValue_bits] using hlen)
    v s hs.bank hs.scratch hs.seven hvWidth hvIndex hvBase hclock
    (by simpa only [addressValue_bits] using harray)
  have hfit' : values.get i<2^width := by
    apply Nat.size_le.mp
    simpa only [Nat.size_eq_bits_len] using hfit
  rw [IncidenceEncoding.words_value width values i hfit'] at hb
  have hwb : width.bits.length≤B := by simpa only [hwidthv] using hv 961 (by decide)
  have hbb : base.bits.length≤B := by simpa only [hbase] using hv 960 (by decide)
  have hib : i.val.bits.length≤B := by simpa only [hindex] using hv 971 (by decide)
  have harr := IncidencePass.array_cost_le width.bits i.val.bits base.bits clock B
    hwb hib hbb (by omega) (by simpa only [addressValue_bits] using hwidthB)
  have htarget := hv target ht
  simp only [addressValue_bits] at hc ha
  refine ⟨cost,t,ex,?_,⟨hb,hz,h7⟩,ha,BankArray.word_of_eq (hf.tapes 962 (by decide) ht₂.symm) hclock,hf⟩
  nlinarith only [hc,harr,htarget,hwidthB,Nat.zero_le B]

#print axioms read_executes
end Maxwell.Continuum.GeometryOutput
