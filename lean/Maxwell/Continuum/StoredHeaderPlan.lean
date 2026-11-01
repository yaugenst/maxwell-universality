import Maxwell.Continuum.StoredNaturalEmission
import Maxwell.Continuum.StoredAmbientPlan
import Maxwell.Cost.Structured.NatAssign.Values
import Maxwell.Cost.Structured.WordCleanup

/-! Header arithmetic reads the retained source, geometric and decoder
selector words. Its fixed plan computes the physical side lengths, report
precision and residual denominator before any of them are serialized. -/
namespace Maxwell.Continuum.StoredHeader
open Maxwell.Cost Maxwell.Cost.Structured RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def inputs : Finset ℕ := {500,501,2216,2221,2237,2240,2241,2242,2244,2245,4427,4428,4701,4702}
def outputList : List ℕ := [720,721,722,723,724,725,726,727,728,729,730,731,732]
def outputs : Finset ℕ := outputList.toFinset
def ids : Finset ℕ := inputs∪outputs
def work : Finset ℕ := {0,1,2,3}∪outputs

def plan : List NatAssign.Instruction :=
  [.literal 729 4,.copy 2221 728,.multiply 2244 728,.add 2221 728,.add 729 728,.literal 729 2,
   .copy 2240 722,.add 728 722,.multiply 729 722,
   .copy 2241 723,.add 728 723,.multiply 729 723,
   .copy 2242 724,.add 728 724,.multiply 729 724,
   .copy 500 720,.copy 501 721,.copy 4427 725,.copy 4428 726,
   .copy 4701 727,.add 4702 727,.literal 729 1,.add 729 727,
   .literal 729 (2^27*64),.copy 501 730,.multiply 729 730,.multiply 2245 730,
   .multiply 2216 730,.multiply 2237 730,.literal 731 0,.literal 732 1]

def initial (v : ℕ→ℕ) (i : ℕ) : ℕ := if i∈outputs then 0 else v i
def prepared (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values plan (initial v)
def prepareCode : Code := .seq (WordCleanup.code outputList) (NatAssign.code plan)
def prepareWidth (B : ℕ) : ℕ := 2^plan.length*(B+1)
def prepareCost (B H : ℕ) : ℕ := outputList.length*(6*H+4)+1+3000*8^plan.length*(B+2)^2

theorem valid : ∀a∈plan,a.Valid ids := by
  simp [plan,NatAssign.Instruction.Valid,ids,inputs,outputs,outputList]

theorem changed : NatAssign.changes plan⊆work := by decide +kernel

theorem literals : ∀a∈plan,a.literalWidth ≤ 34 := by
  decide +kernel

theorem prepared_kept (v : ℕ→ℕ) (i : ℕ) (hi : i∉outputs) : prepared v i=v i := by
  rw [prepared,NatAssign.values_preserves]
  · exact ite_eq_right hi
  · intro a ha
    have target : a.target∈outputs := by
      have h : ∀a∈plan,a.target∈outputs := by decide +kernel
      exact h a ha
    intro he
    apply hi
    rwa [he]

theorem prepared_nats (v : ℕ→ℕ) :
    StoredNatural.continuumHeaderPorts.map (prepared v)=
      [v 500,v 501,StoredAmbient.side v 0,StoredAmbient.side v 1,StoredAmbient.side v 2,
       v 4427,v 4428,v 4701+v 4702+1] := by
  simp [StoredNatural.continuumHeaderPorts,prepared,plan,initial,outputs,outputList,
    NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,StoredAmbient.side]
  all_goals (repeat' constructor) <;> ring

theorem prepared_fraction (v : ℕ→ℕ) :
    prepared v 730=2^27*64*v 501*v 2245*v 2216*v 2237 ∧
      prepared v 731=0 ∧ prepared v 732=1 := by
  change v 2237*(v 2216*(v 2245*((2^27*64)*v 501)))=
    2^27*64*v 501*v 2245*v 2216*v 2237 ∧(0:ℕ)=0 ∧(1:ℕ)=1
  exact ⟨by ac_rfl,rfl,rfl⟩

theorem prepare_executes (v : ℕ→ℕ) (B H : ℕ) (hB : 34 ≤ B)
    (width : ∀i∈inputs,(v i).bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank inputs v s.val) (scratch : NatAssign.Scratch s.val)
    (old : WordCleanup.Bounded outputList H s.val) :
    ∃cost t,Executes input tape prepareCode cost s t ∧cost ≤ prepareCost B H ∧
      NatAssign.Bank ids (prepared v) t.val ∧NatAssign.Scratch t.val ∧
      (∀i∈ids,(prepared v i).bits.length ≤ prepareWidth B) ∧
      BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨c,a,e,hc,blank,frame⟩:=WordCleanup.executes outputList H input tape s old
  have initialBank : NatAssign.Bank ids (initial v) a.val := by
    intro i hi
    by_cases ho : i∈outputs
    · simpa only [initial,ite_eq_left ho] using (zero_word_iff_blank _ _).mpr
        (blank i (List.mem_toFinset.mp ho))
    · have hin : i∈inputs := (Finset.mem_union.mp hi).resolve_right ho
      simpa only [initial,ite_eq_right ho] using word_of_eq (frame.tapes i ho) (bank i hin)
  have initialWidth : ∀i∈ids,(initial v i).bits.length ≤ B := by
    intro i hi
    by_cases ho : i∈outputs
    · simp [initial,ho]
    · simpa only [initial,ite_eq_right ho] using width i ((Finset.mem_union.mp hi).resolve_right ho)
  have lower : ∀i∈ids,4 ≤ i := by decide +kernel
  have scratchA : NatAssign.Scratch a.val := by
    intro i hi
    exact blank_of_eq (frame.tapes i (by simp [outputList];omega)) (scratch i hi)
  obtain ⟨d,t,ed,hd,bt,zt,ft⟩:=NatAssign.executes ids lower plan valid (initial v)
    input tape a initialBank scratchA
  have price:=NatAssign.price_bound ids plan valid (initial v) B initialWidth
    (fun q hq=>(literals q hq).trans hB)
  have bits:=NatAssign.values_width ids plan valid (initial v) B initialWidth
    (fun q hq=>(literals q hq).trans hB)
  exact ⟨c+d,t,e.seq ed,Nat.add_le_add hc (hd.trans price),bt,zt,
    fun i hi=>Nat.le_of_succ_le (bits i hi),
    (frame.mono (Finset.subset_union_right)).trans (ft.mono changed)⟩

#print axioms prepare_executes
end Maxwell.Continuum.StoredHeader
