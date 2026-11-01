import Maxwell.Cost.RationalCanonical.PreparedEmission
import Maxwell.Cost.Structured.WordMagnitude

/-! Canonical output of a signed fraction from its actual three natural
channels. Subtraction, cleanup, GCD reduction and serialization are executed;
the original channels survive, so the same routine serves either encoding. -/
namespace Maxwell.Cost.RationalCanonical.StoredEmission
open Structured RationalAccumulator
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def words : List ℕ := [0,1,2,3,4,220,221,222,223,228,229,230,231]
def work : Finset ℕ := words.toFinset

def prepareCode (positive negative denominator : ℕ) : Code :=
  .seq (WordCleanup.code words)
    (.seq (WordMagnitude.code positive negative 228)
      (.call (WordTransfer.clone denominator 229)))

def code (positive negative denominator : ℕ) : Code :=
  .seq (prepareCode positive negative denominator)
    RationalCanonical.code

def prepareCost (B H : ℕ) : ℕ := 13*(6*H+4)+1+300*(2*B+4)+15*B+17
def costBound (B H : ℕ) : ℕ := prepareCost B H+100000*(2*B+3)^3

theorem bounded {s : BitRAMState} {a b B : ℕ} (ready : NormalizeReady s a b)
    (aw : a.bits.length ≤ B) (bw : b.bits.length ≤ B) : WordCleanup.Bounded words B s := by
  intro i hi
  by_cases hn : i=228
  · subst i
    exact ⟨a.bits,aw,ready.numerator⟩
  by_cases hd : i=229
  · subst i
    exact ⟨b.bits,bw,ready.denominator⟩
  refine ⟨[],Nat.zero_le _,?_⟩
  apply (zero_word_iff_blank _ _).mpr
  apply ready.workspace_blank i
  simp only [words,List.mem_cons,List.not_mem_nil,or_false] at hi
  simp only [workspace,List.mem_cons,List.not_mem_nil,or_false]
  omega

theorem prepares (positive negative denominator x y d B H : ℕ)
    (hp : 232 ≤ positive) (hn : 232 ≤ negative) (hd : 232 ≤ denominator)
    (xw : x.bits.length ≤ B) (yw : y.bits.length ≤ B)
    (dw : d.bits.length ≤ B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (px : Word s.val positive x) (ny : Word s.val negative y) (dd : Word s.val denominator d)
    (old : WordCleanup.Bounded words H s.val) :
    ∃cost t,Executes input tape (prepareCode positive negative denominator) cost s t ∧
      cost ≤ prepareCost B H ∧ NormalizeReady t.val (IntegerNormSquare.magnitude x y) d ∧
      BinaryPrecision.Frame work s.val t.val ∧
      t.val.registers 23=SignedDifference.sign x.bits y.bits := by
  obtain ⟨c,a,e0,hc,blank,frame⟩:=WordCleanup.executes words H input tape s old
  have outside (i : ℕ) (hi : 232 ≤ i) : i∉work := by
    simp only [work,words,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
    omega
  obtain ⟨c1,b,e1,hc1,num,z,frame1,sign⟩:=WordMagnitude.executes positive negative 228
    (by omega) (by omega) (by decide) input tape x y a
    (word_of_eq (frame.tapes positive (outside positive hp)) px)
    (word_of_eq (frame.tapes negative (outside negative hn)) ny)
    (blank 228 (by decide)) (fun i hi=>blank i (by simp [words];omega))
  have f1 : BinaryPrecision.Frame work s.val b.val:=frame.trans (frame1.mono (by decide))
  obtain ⟨origin,den⟩:=word_of_eq (f1.tapes denominator (outside denominator hd)) dd
  obtain ⟨outOrigin,target⟩:=blank_of_eq (frame1.tapes 229 (by decide)) (blank 229 (by decide))
  obtain ⟨t,e2,tapes,frame2⟩:=WordCall.clone denominator 229 (by omega) input tape d.bits
    origin outOrigin b den target
  have keep (i : ℕ) (hi : i≠229) : t.val.tapes i=b.val.tapes i := by
    simp only [tapes,Function.update_of_ne hi]
  have allBlank (i : ℕ) (hi : i∈workspace) : Blank t.val i := by
    have neq : i≠229 ∧ i∉({0,1,2,228}:Finset ℕ) ∨ i<4 := by
      simp only [workspace,List.mem_cons,List.not_mem_nil,or_false] at hi
      simp only [Finset.mem_insert,Finset.mem_singleton]
      omega
    rcases neq with ⟨n229,nwork⟩|small
    · exact blank_of_eq ((keep i n229).trans (frame1.tapes i nwork))
        (blank i (by
          simp only [workspace,List.mem_cons,List.not_mem_nil,or_false] at hi
          simp only [words,List.mem_cons,List.not_mem_nil,or_false]
          tauto))
    · exact blank_of_eq (keep i (by omega)) (z i small)
  refine ⟨c+(c1+(15*d.bits.length+17)),t,e0.seq (e1.seq e2),?_,?_,?_,?_⟩
  · change c ≤ 13*(6*H+4)+1 at hc
    unfold prepareCost
    omega
  · exact ⟨word_of_eq (keep 228 (by decide)) num,⟨outOrigin,by simp [tapes]⟩,
      ⟨(zero_word_iff_blank _ _).mpr (allBlank 220 (by decide)),
       (zero_word_iff_blank _ _).mpr (allBlank 221 (by decide)),
       allBlank 222 (by decide),allBlank 223 (by decide),
       fun i hi=>allBlank i (by simp [workspace];omega)⟩,
      allBlank 230 (by decide),allBlank 231 (by decide)⟩
  · exact ⟨frame2.1.trans f1.address,frame2.2.1.trans f1.inputHead,
      frame2.2.2.1.trans f1.memory,frame2.2.2.2.1.trans f1.randomCursor,
      frame2.2.2.2.2.1.trans f1.output,fun i hi=>
        (keep i (by intro h;subst i;exact hi (by decide))).trans (f1.tapes i hi)⟩

  · exact (frame2.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide)).trans sign

theorem executes (positive negative denominator x y d B H : ℕ)
    (hp : 232 ≤ positive) (hn : 232 ≤ negative) (hd : 232 ≤ denominator)
    (dpos : 0<d) (xw : x.bits.length ≤ B) (yw : y.bits.length ≤ B)
    (dw : d.bits.length ≤ B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (px : Word s.val positive x) (ny : Word s.val negative y) (dd : Word s.val denominator d)
    (old : WordCleanup.Bounded words H s.val) :
    ∃cost t,Executes input tape (code positive negative denominator) cost s t ∧
      cost ≤ costBound B H ∧
      t.val.output=(Codec.rat (((x:ℚ)-y)/d)).reverse++s.val.output ∧
      NormalizeReady t.val (IntegerNormSquare.magnitude x y) d ∧
      t.val.address=s.val.address ∧ t.val.memory=s.val.memory ∧
      t.val.inputHead=s.val.inputHead ∧ t.val.randomCursor=s.val.randomCursor ∧
      (∀i,i∉work→t.val.tapes i=s.val.tapes i) := by
  obtain ⟨c,a,e0,hc,ready,frame,sign⟩:=prepares positive negative denominator x y d B H
    hp hn hd xw yw dw input tape s px ny dd old
  obtain ⟨c1,t,hc1,e1,out,done,f1⟩:=RationalCanonical.executes input tape
    (SignedDifference.sign x.bits y.bits) (IntegerNormSquare.magnitude x y) d dpos a ready sign
  refine ⟨c+c1,t,e0.seq e1,?_,?_,done,
    f1.address.trans frame.address,f1.memory.trans frame.memory,
    f1.inputHead.trans frame.inputHead,f1.randomCursor.trans frame.randomCursor,
    fun i hi=>(f1.tapes i (by simpa [work,words] using hi)).trans (frame.tapes i hi)⟩
  · have diffWidth : (IntegerNormSquare.magnitude x y).size ≤ B+1 := by
      rw [←Nat.size_eq_bits_len]
      exact (IntegerNormSquare.magnitude_bits_length_le x y).trans (by omega)
    have denWidth : d.size ≤ B := by simpa only [Nat.size_eq_bits_len] using dw
    have hpw : ((IntegerNormSquare.magnitude x y).size+d.size+2)^3 ≤ (2*B+3)^3 :=
      Nat.pow_le_pow_left (by omega) 3
    have total:=hc1.trans ((RationalCanonical.costBound_polynomial _ d).trans
      (Nat.mul_le_mul_left 100000 hpw))
    unfold costBound
    omega
  · rw [out,frame.output]
    have represented := SignedDifference.signed_value x.bits y.bits
    rw [IntegerNormSquare.magnitude_eq,RationalAccumulator.address_bits,
      RationalAccumulator.address_bits] at represented
    have value_eq : value (SignedDifference.sign x.bits y.bits)
        (IntegerNormSquare.magnitude x y) d=((x:ℚ)-y)/d := by
      unfold value
      have cast := congrArg (fun z:ℤ=>(z:ℚ)) represented
      cases hsign : SignedDifference.sign x.bits y.bits <;>
        simp [hsign] at cast ⊢ <;> rw [←cast]
    rw [value_eq]

#print axioms executes
end Maxwell.Cost.RationalCanonical.StoredEmission
