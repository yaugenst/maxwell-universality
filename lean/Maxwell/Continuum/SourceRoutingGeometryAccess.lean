import Maxwell.Continuum.SourceRoutingGeometryArithmetic

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryArithmetic
open Structured
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

theorem bank_frame {v : ℕ→ℕ} {s t : BitRAMState} {changed : Finset ℕ}
    (bank : NatAssign.Bank ids v s) (frame : ArchiveFrame changed s t)
    (disjoint : Disjoint ids changed) : NatAssign.Bank ids v t := by
  intro i hi
  exact RationalAccumulator.word_of_eq (frame.tapes i (Or.inr (by have h:=ids_lower i hi;omega))
    (Finset.disjoint_left.mp disjoint hi)) (bank i hi)

theorem read {n : ℕ} (widthBank indexBank baseBank clockBank target : ℕ)
    (hwBank : 40 ≤ widthBank) (hiBank : 40 ≤ indexBank) (hbBank : 40 ≤ baseBank)
    (hcBank : 40 ≤ clockBank) (htarget : target∈controls)
    (width base B : ℕ) (clock : List Bool) (values : Vector ℕ n) (i : Fin n)
    (hwidth : 0<width) (hclock : clock.length=width)
    (hfit : (values.get i).bits.length ≤ width) (hw : width ≤ B)
    (hi : i.val.bits.length ≤ B) (hb : base.bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (v : ℕ→ℕ) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (ready : GeometryArray.Ready s.val)
    (privateBlank : Blank s.val 1249) (zero : v target=0)
    (ww : Word s.val widthBank width) (iw : Word s.val indexBank i.val)
    (bw : Word s.val baseBank base) (cw : BankArray.Word s.val clockBank clock)
    (stored : BitArray.Represents s.val.memory base width (IncidenceEncoding.words width values)) :
    ∃steps t,Executes input tape (BankArray.readCanonicalCode widthBank indexBank baseBank clockBank target) steps s t ∧
      steps ≤ 2^20*(B+3)^2 ∧ NatAssign.Bank ids (Function.update v target (values.get i)) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ t.val.memory=s.val.memory ∧
      ArchiveFrame {target} s.val t.val := by
  have targetMember : target∈ids := Finset.mem_union_left _ htarget
  have hz : Blank s.val target := (RationalAccumulator.zero_word_iff_blank _ _).mp
    (by simpa only [zero] using bank target targetMember)
  obtain ⟨steps,t,he,hcost,word,zt,mt,ft⟩:=GeometryArray.read widthBank indexBank baseBank clockBank target
    hwBank hiBank hbBank hcBank (ids_lower target targetMember) width base B clock values i
    hwidth hclock hfit hw hi hb input tape s ready hz ww iw bw cw stored
  have bt : NatAssign.Bank ids (Function.update v target (values.get i)) t.val := by
    intro j hj
    by_cases heq : j=target
    · subst j
      simpa only [Function.update_self] using word
    · rw [Function.update_of_ne heq]
      exact RationalAccumulator.word_of_eq (ft.tapes j (Or.inr (by have h:=ids_lower j hj;omega))
        (by simpa only [Finset.mem_singleton] using heq)) (bank j hj)
  refine ⟨steps,t,he,hcost,bt,zt,RationalAccumulator.blank_of_eq (ft.tapes 1249 (by omega) ?_) privateBlank,mt,ft⟩
  simp only [controls,Finset.mem_Icc] at htarget
  simp only [Finset.mem_singleton]
  omega

theorem write {n : ℕ} (widthBank indexBank baseBank clockBank source : ℕ)
    (hwBank : 40 ≤ widthBank) (hiBank : 40 ≤ indexBank) (hbBank : 40 ≤ baseBank)
    (hcBank : 40 ≤ clockBank) (hsBank : 40 ≤ source)
    (width base B value : ℕ) (clock : List Bool) (words : Vector (List Bool) n) (i : Fin n)
    (hwidth : 0<width) (hclock : clock.length=width) (hfit : value.bits.length ≤ width)
    (hw : width ≤ B) (hi : i.val.bits.length ≤ B) (hb : base.bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (v : ℕ→ℕ) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249)
    (ww : Word s.val widthBank width) (iw : Word s.val indexBank i.val)
    (bw : Word s.val baseBank base) (cw : BankArray.Word s.val clockBank clock)
    (vw : Word s.val source value) (stored : BitArray.Represents s.val.memory base width words) :
    ∃steps t,Executes input tape (BankArray.writeCanonicalCode widthBank indexBank baseBank clockBank source) steps s t ∧
      steps ≤ 2^20*(B+3)^2 ∧ NatAssign.Bank ids v t.val ∧ GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧
      t.val.memory=MemoryWord.writeBits s.val.memory (base+i.val*width) (IncidenceEncoding.word width value) ∧
      BitArray.Represents t.val.memory base width (words.set i (IncidenceEncoding.word width value)) ∧
      ArchiveFrame {37} s.val t.val := by
  obtain ⟨steps,t,he,hcost,zt,mt,st,ft⟩:=GeometryArray.write widthBank indexBank baseBank clockBank source
    hwBank hiBank hbBank hcBank hsBank width base B value clock words i hwidth hclock hfit hw hi hb
    input tape s ready ww iw bw cw vw stored
  exact ⟨steps,t,he,hcost,bank_frame bank ft (by decide),zt,
    RationalAccumulator.blank_of_eq (ft.tapes 1249 (by omega) (by decide)) privateBlank,mt,st,ft⟩

#print axioms read
#print axioms write
end Maxwell.Cost.RoutingPorts.Complete.GeometryArithmetic
