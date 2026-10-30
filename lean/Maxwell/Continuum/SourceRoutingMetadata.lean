import Maxwell.Continuum.SourceRoutingMetadataPlan
import Maxwell.Continuum.NatAssignOutputWidth
import Maxwell.Continuum.SourceRoutingAccessCost

/-! Runtime construction of the complete routing-array descriptor. The
word width is obtained by scanning the computed count. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Startup
open Structured
open RationalAccumulator (Word Blank)
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def work : Finset ℕ := {0,1,2,3,709,711,712,716,717,718,719}
def measuredValues (v : ℕ→ℕ) : ℕ→ℕ :=
  Function.update (countValues v) 711 (4*v 705).bits.length
def metadataCode : Code := .seq (NatAssign.code countStatements)
  (.seq (WordLength.code 709 711) (NatAssign.code addressStatements))

theorem ready_scratch {s : BitRAMState} (hs : Ready s) : NatAssign.Scratch s := by
  intro i hi
  interval_cases i
  · exact hs.scratch.1
  · exact hs.scratch.2.1
  · exact hs.scratch.2.2.1
  · exact hs.scratch.2.2.2.1

theorem ready_of_binary {s t : BitRAMState} {changed : Finset ℕ}
    (hs : Ready s) (hz : NatAssign.Scratch t) (hf : BinaryPrecision.Frame changed s t)
    (hchange : ∀i∈changed,i<4 ∨ (700 ≤ i ∧ i<752)) : Ready t := by
  have keep (i : ℕ) (hi : 4 ≤ i) (hlo : i<700 ∨ 752 ≤ i) : t.tapes i=s.tapes i :=
    hf.tapes i (by intro h; have := hchange i h; omega)
  rcases hs.scratch with ⟨_,_,_,_,h5,h6,h8,h9⟩
  exact ⟨⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),
    RationalAccumulator.blank_of_eq (keep 5 (by decide) (by decide)) h5,
    RationalAccumulator.blank_of_eq (keep 6 (by decide) (by decide)) h6,
    RationalAccumulator.blank_of_eq (keep 8 (by decide) (by decide)) h8,
    RationalAccumulator.blank_of_eq (keep 9 (by decide) (by decide)) h9⟩,
    RationalAccumulator.blank_of_eq (keep 7 (by decide) (by decide)) hs.seven,
    RationalAccumulator.blank_of_eq (keep 37 (by decide) (by decide)) hs.pack,
    RationalAccumulator.blank_of_eq (keep 752 (by decide) (by decide)) hs.probe⟩

theorem count_width (v : ℕ→ℕ) (B : ℕ) (hB : 3≤B)
    (hw : ∀i∈ids,(v i).bits.length≤B) :
    ∀i∈ids,(countValues v i).bits.length+1≤64*(B+1) := by
  exact NatAssign.values_width_bound ids countStatements count_valid v B hw (by
    simp only [countStatements,List.mem_cons,List.not_mem_nil,or_false]
    intro a ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals norm_num [NatAssign.Instruction.literalWidth,show (4 : ℕ).bits.length=3 by decide]
    omega)

theorem measured_width (v : ℕ→ℕ) (B : ℕ) (hB : 3≤B)
    (hw : ∀i∈ids,(v i).bits.length≤B) :
    ∀i∈ids,(measuredValues v i).bits.length≤64*(B+1) := by
  have hc := count_width v B hB hw
  intro i hi
  by_cases he : i=711
  · subst i
    simp only [measuredValues,Function.update_self]
    have hn := hc 709 (by decide)
    rw [count_count] at hn
    exact (natural_bits_length_le _).trans (by omega)
  · simpa only [measuredValues,Function.update_of_ne he] using (hc i hi).trans' (Nat.le_succ _)

theorem metadata_executes (v : ℕ→ℕ) (h711 : v 711=0) (h705 : 0<v 705)
    (B : ℕ) (hB : 3≤B) (hw : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids v s.val) (hz : Ready s.val) :
    ∃steps t, Executes input tape metadataCode steps s t ∧ steps≤2^60*(B+2)^2 ∧
      Ready t.val ∧ Metadata (layout (4*v 705) (v 145+4*v 141) (by positivity)) t.val ∧
      Word t.val 719 (v 145+4*v 141+2*((4*v 705)*(4*v 705).bits.length)) ∧
      Blank t.val 712 ∧ BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨c0,a,e0,hc0,ba,za,fa⟩ := count_executes v B hB hw input tape s hs (ready_scratch hz)
  have a709 : Word a.val 709 (4*v 705) := by
    simpa only [count_count] using ba 709 (by decide)
  have a711 : Blank a.val 711 := by
    have h := ba 711 (by decide)
    rw [count_other v 711 (by decide) (by decide) (by decide),h711] at h
    exact (RationalAccumulator.zero_word_iff_blank _ _).mp h
  obtain ⟨c1,b,e1,hc1,b711,fb⟩ := RoutingPorts.wordLength 709 711 (by decide)
    input tape (4*v 705) a a709 a711
  have bb : NatAssign.Bank ids (measuredValues v) b.val := by
    intro i hi
    by_cases he : i=711
    · subst i
      exact b711
    · simp only [measuredValues,Function.update_of_ne he]
      exact RationalAccumulator.word_of_eq (fb.tapes i (by simpa using he)) (ba i hi)
  have zb : NatAssign.Scratch b.val := by
    intro i hi
    exact RationalAccumulator.blank_of_eq (fb.tapes i (by simp; omega)) (za i hi)
  obtain ⟨c2,t,e2,hc2,bt,zt,ft⟩ := address_executes (measuredValues v) (64*(B+1))
    (measured_width v B hB hw) input tape b bb zb
  have vm709 : measuredValues v 709=4*v 705 := by simp [measuredValues,count_count]
  have vm716 : measuredValues v 716=v 145+4*v 141 := by simp [measuredValues,count_base]
  have vm711 : measuredValues v 711=(measuredValues v 709).bits.length := by
    simp [measuredValues,count_count]
  have vp : 0<measuredValues v 709 := by rw [vm709]; positivity
  obtain ⟨mt,et,clear⟩ := address_metadata (measuredValues v) vm711 vp t.val bt
  simp only [vm709,vm716] at mt et
  have frame : BinaryPrecision.Frame work s.val t.val :=
    (fa.mono (by decide)).trans ((fb.mono (by decide)).trans (ft.mono (by decide)))
  have rt := ready_of_binary hz zt frame (by
    intro i hi
    simp only [work,Finset.mem_insert,Finset.mem_singleton] at hi
    omega)
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,rt,mt,et,clear,frame⟩
  have hn := count_width v B hB hw 709 (by decide)
  rw [count_count] at hn
  have hp : ((4*v 705).bits.length+1)^2 ≤ (64*(B+1)+2)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hq : (64*(B+1)+2)^2 ≤ 4356*(B+2)^2 := by
    calc
      _ ≤ (66*(B+2))^2 := Nat.pow_le_pow_left (by omega) 2
      _ = _ := by ring
  nlinarith only [hc0,hc1,hc2,hp,hq,Nat.one_le_pow 2 (B+2) (by omega)]

#print axioms metadata_executes

end Maxwell.Cost.RoutingPorts.Complete.Startup
