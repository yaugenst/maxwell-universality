import Maxwell.Continuum.RationalDataflowNaturalChannels
import Maxwell.Continuum.CalibrationElementaryFrames

/-! Construct a rational register directly from two stored natural words.
Both channel copies and the reset of the previous target are charged. -/
namespace Maxwell.Continuum.RationalDataflow.FractionWord
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 2500000

def part (a b : ℕ) : Parts := ⟨a,0,b⟩
def code (sourceNumerator sourceDenominator target : ℕ) : Code :=
  .seq (Instruction.literal target 0).code
    (.seq (NaturalChannel.code .positive sourceNumerator target)
      (NaturalChannel.code .denominator sourceDenominator target))

theorem outside (S : Finset ℕ) (i : ℕ) (hi : 300 ≤ i ∧ i<1000) :
    i∉workspace S := by
  have hp := RootSample.small_not_ports S i hi.2
  simp only [workspace,ids,workPorts,temporaryPorts,RationalMagnitude.ids,
    Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  exact not_or_intro (by omega) (not_or_intro hp (by omega))

theorem executes (S : Finset ℕ) (sourceNumerator sourceDenominator target : ℕ)
    (ha : 300 ≤ sourceNumerator ∧ sourceNumerator<1000)
    (hb : 300 ≤ sourceDenominator ∧ sourceDenominator<1000) (ht : target∈S)
    (a b W : ℕ) (v : ℕ→Parts) (hw : WidthBank S W v) (hW : 1≤W)
    (haW : a.bits.length≤W) (hbW : b.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s)
    (wa : Word s.val sourceNumerator a) (wb : Word s.val sourceDenominator b) :
    ∃cost t,Executes input tape (code sourceNumerator sourceDenominator target) cost s t ∧
      cost≤2^103*(W+3)^2 ∧ Ready S (Function.update v target (part a b)) t ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  have hz : (Parts.literal 0).Width W :=
    (show (Parts.literal 0).Width 1 by change 0≤1 ∧ 0≤1 ∧ 1≤1;omega).mono hW
  obtain ⟨c0,s0,e0,h0,b0,f0⟩ := (Instruction.literal target 0).executes S ht v W hw hz input tape s hs
  have a0 := word_of_eq (f0.tapes sourceNumerator (outside S _ ha)) wa
  have b0' := word_of_eq (f0.tapes sourceDenominator (outside S _ hb)) wb
  have hp := NaturalChannel.port_ge .positive target
  obtain ⟨c1,s1,e1,h1,b1,f1⟩ := NaturalChannel.executes S .positive sourceNumerator target ht
    (by omega) (Function.update v target (Parts.literal 0)) a.bits input tape s0 b0 a0
  have b1' := word_of_eq (f1.tapes sourceDenominator (by simp only [Finset.mem_singleton];omega)) b0'
  have hd := NaturalChannel.port_ge .denominator target
  have b1'' : Ready S (Function.update v target (part a 1)) s1 := by
    simpa only [addressValue_bits,Function.update_self,NaturalChannel.replace,Parts.literal,
      show (0:ℚ).num=0 by rfl,show (0:ℚ).den=1 by rfl,Int.toNat_zero,neg_zero,
      Function.update_idem,part] using b1
  obtain ⟨c2,t,e2,h2,b2,f2⟩ := NaturalChannel.executes S .denominator sourceDenominator target ht
    (by omega) (Function.update v target (part a 1)) b.bits input tape s1 b1'' b1'
  have b2' : Ready S (Function.update v target (part a b)) t := by
    simpa only [addressValue_bits,Function.update_self,NaturalChannel.replace,part,Function.update_idem] using b2
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,b2',f0.trans ((f1.mono ?_).trans (f2.mono ?_))⟩
  · simp only [NaturalChannel.port,dataValues_positive,Function.update_self,Parts.literal,
      show (0:ℚ).num=0 by rfl,Int.toNat_zero,show (0:ℕ).bits.length=0 by rfl] at h1
    simp only [NaturalChannel.port,dataValues_denominator,Function.update_self,part,
      show (1:ℕ).bits.length=1 by rfl] at h2
    unfold operationCost at h0
    have hpw : 1≤(W+3)^2 := one_le_pow₀ (by omega)
    have hWsq : W≤(W+3)^2 := by nlinarith
    nlinarith only [h0,h1,h2,haW,hbW,hpw,hWsq]
  · intro i hi
    have he : i=NaturalChannel.port .positive target := by simpa only [Finset.mem_singleton] using hi
    subst i
    exact Finset.mem_union_right _ (NaturalChannel.port_mem .positive S target ht)
  · intro i hi
    have he : i=NaturalChannel.port .denominator target := by simpa only [Finset.mem_singleton] using hi
    subst i
    exact Finset.mem_union_right _ (NaturalChannel.port_mem .denominator S target ht)

#print axioms executes
end Maxwell.Continuum.RationalDataflow.FractionWord
