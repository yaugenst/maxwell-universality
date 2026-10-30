import Maxwell.Continuum.SourceRoutingAccessCost
import Maxwell.Continuum.SourceRoutingArchiveFrame
import Maxwell.Cost.BankArray.ReadCanonical

/-! Charged natural-array operations used by the continuum geometry program. -/

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryArray
open Structured
open RationalAccumulator (Blank Word)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

structure Ready (s : BitRAMState) : Prop where
  scratch : BankArray.Scratch s
  seven : Blank s 7
  pack : Blank s 37

def snapshot (memory : ℕ→Bool) (base width n : ℕ) : Vector (List Bool) n :=
  Vector.ofFn (fun i => MemoryWord.readBits memory (base+i.val*width) width)

theorem snapshot_represents (memory : ℕ→Bool) (base width n : ℕ) :
    BitArray.Represents memory base width (snapshot memory base width n) := by
  refine ⟨?_,?_⟩
  · intro i
    simp [snapshot,Vector.get,Fin.cast]
  · intro i j hj
    simp [snapshot,Vector.get,Fin.cast,MemoryWord.readBits_getElem,hj]

theorem access_bound (width index base B : ℕ) (clock : List Bool)
    (hclock : clock.length=width) (hw : width ≤ B) (hi : index.bits.length ≤ B)
    (hb : base.bits.length ≤ B) :
    BankArray.costCap width.bits index.bits base.bits clock+102*width+100 ≤ 2^20*(B+3)^2 := by
  have hwidth:=(natural_bits_length_le width).trans hw
  have h:=access_cost_bound width index base (2*(B+3)) clock hclock
    (by omega) (by omega) (by omega)
  nlinarith only [h]

theorem read {n : ℕ} (widthBank indexBank baseBank clockBank target : ℕ)
    (hwBank : 40 ≤ widthBank) (hiBank : 40 ≤ indexBank) (hbBank : 40 ≤ baseBank)
    (hcBank : 40 ≤ clockBank) (htBank : 40 ≤ target)
    (width base B : ℕ) (clock : List Bool) (values : Vector ℕ n) (i : Fin n)
    (hwidth : 0<width) (hclock : clock.length=width)
    (hfit : (values.get i).bits.length ≤ width) (hw : width ≤ B)
    (hi : i.val.bits.length ≤ B) (hb : base.bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready s.val)
    (htarget : Blank s.val target)
    (ww : Word s.val widthBank width) (iw : Word s.val indexBank i.val)
    (bw : Word s.val baseBank base) (cw : BankArray.Word s.val clockBank clock)
    (stored : BitArray.Represents s.val.memory base width (IncidenceEncoding.words width values)) :
    ∃steps t,Executes input tape (BankArray.readCanonicalCode widthBank indexBank baseBank clockBank target) steps s t ∧
      steps ≤ 2^20*(B+3)^2 ∧ Word t.val target (values.get i) ∧ Ready t.val ∧
      t.val.memory=s.val.memory ∧ ArchiveFrame {target} s.val t.val := by
  obtain ⟨steps,t,hcost,he,wt,zt,t7,mt,_,ft⟩:=BankArray.read_canonical
    widthBank indexBank baseBank clockBank target (by omega) (by omega) (by omega) (by omega) (by omega)
    input tape width.bits i.val.bits base.bits clock (IncidenceEncoding.words width values) i
    (RationalAccumulator.bits_nonempty hwidth) (addressValue_bits _)
    (by simpa only [addressValue_bits] using hclock) s hs.scratch hs.seven htarget ww iw bw cw
    (by simpa only [addressValue_bits] using stored)
  have value : addressValue ((IncidenceEncoding.words width values).get i)=values.get i := by
    rw [IncidenceEncoding.words_get,IncidenceEncoding.word,FixedWidth.bits_value _ _ hfit,addressValue_bits]
  simp only [addressValue_bits] at hcost
  have cap:=access_bound width i.val base B clock hclock hw hi hb
  exact ⟨steps,t,he,by omega,by simpa only [value] using wt,
    ⟨zt,t7,RationalAccumulator.blank_of_eq (ft.2.2.2.1 37 (by omega) (by omega)) hs.pack⟩,
    mt,ArchiveFrame.of_bank ft⟩

theorem write {n : ℕ} (widthBank indexBank baseBank clockBank source : ℕ)
    (hwBank : 40 ≤ widthBank) (hiBank : 40 ≤ indexBank) (hbBank : 40 ≤ baseBank)
    (hcBank : 40 ≤ clockBank) (hsBank : 40 ≤ source)
    (width base B value : ℕ) (clock : List Bool) (words : Vector (List Bool) n) (i : Fin n)
    (hwidth : 0<width) (hclock : clock.length=width) (hfit : value.bits.length ≤ width)
    (hw : width ≤ B) (hi : i.val.bits.length ≤ B) (hb : base.bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready s.val)
    (ww : Word s.val widthBank width) (iw : Word s.val indexBank i.val)
    (bw : Word s.val baseBank base) (cw : BankArray.Word s.val clockBank clock)
    (vw : Word s.val source value) (stored : BitArray.Represents s.val.memory base width words) :
    ∃steps t,Executes input tape (BankArray.writeCanonicalCode widthBank indexBank baseBank clockBank source) steps s t ∧
      steps ≤ 2^20*(B+3)^2 ∧ Ready t.val ∧
      t.val.memory=MemoryWord.writeBits s.val.memory (base+i.val*width) (IncidenceEncoding.word width value) ∧
      BitArray.Represents t.val.memory base width (words.set i (IncidenceEncoding.word width value)) ∧
      ArchiveFrame {37} s.val t.val := by
  obtain ⟨steps,t,hcost,he,mt,st,zt,t7,t37,ft⟩:=BankArray.write_canonical
    widthBank indexBank baseBank clockBank source (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
    input tape width.bits i.val.bits base.bits clock words i value
    (RationalAccumulator.bits_nonempty hwidth) (addressValue_bits _)
    (by simpa only [addressValue_bits] using hclock)
    (by simpa only [addressValue_bits] using hwidth)
    (by simpa only [addressValue_bits] using hfit)
    s hs.scratch hs.seven hs.pack ww iw bw cw vw (by simpa only [addressValue_bits] using stored)
  simp only [addressValue_bits] at hcost mt st
  have cap:=access_bound width i.val base B (FixedWidth.bits width value.bits)
    (FixedWidth.bits_length _ _) hw hi hb
  exact ⟨steps,t,he,by omega,⟨zt,t7,t37⟩,mt,st,ArchiveFrame.of_bank ft⟩

#print axioms read
#print axioms write
end Maxwell.Cost.RoutingPorts.Complete.GeometryArray
