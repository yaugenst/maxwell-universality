import Maxwell.Continuum.EdgeBracketWords
import Maxwell.Continuum.EdgeInitialWidths
import Maxwell.Cost.Structured.NatAssign.Literals

/-! The initial bracket is input-independent finite data. Its literal writes
are executed and charged; subsequent brackets are computed by integer updates. -/
namespace Maxwell.Continuum.Calibration.EdgeBracketMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Certificate RationalDataflow
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
attribute [local irreducible] edgeInitial EdgeWords.ofInterval

def initial (I : Interval) (i : ℕ) : ℕ :=
  let w:=EdgeWords.ofInterval I
  if i=base then w.lower.toNat
  else if i=base+1 then (-w.lower).toNat
  else if i=base+2 then w.denominator
  else if i=base+3 then w.upper.toNat
  else if i=base+4 then (-w.upper).toNat
  else if i=base+5 then w.denominator
  else if i=base+8 then 1 else 0

theorem initial_words (I : Interval) : words (initial I)=EdgeWords.ofInterval I := by
  simp only [words,initial]
  norm_num

theorem initial_denominators (I : Interval) : Denominators (initial I) := by
  norm_num [Denominators,initial]
  exact EdgeWords.ofInterval_den_pos I

theorem initial_width (I : Interval) (W : ℕ)
    (lo : RationalWords.Width I.lo W) (hi : RationalWords.Width I.hi W) :
    ∀i∈SignedBracket.ids base,((initial I) i).bits.length≤2*W+2 := by
  obtain ⟨lower,upper,denominator⟩:=EdgeWords.ofInterval_bound I W lo hi
  have nonnegative (z : ℤ) : z.toNat≤z.natAbs := by cases z <;> simp
  have lp:=nonnegative (EdgeWords.ofInterval I).lower
  have ln:=nonnegative (-(EdgeWords.ofInterval I).lower)
  have up:=nonnegative (EdgeWords.ofInterval I).upper
  have un:=nonnegative (-(EdgeWords.ofInterval I).upper)
  rw [Int.natAbs_neg] at ln un
  have hp : 0<(2:ℕ)^(2*W) := by positivity
  intro i _
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have size : initial I i≤2^(2*W) := by
    unfold initial
    dsimp only
    split_ifs <;> omega
  rw [pow_add]
  norm_num
  omega

def initializeCode : Code := NatAssign.Literals.code (SignedBracket.ids base) (initial edgeInitial)
def initialWidth : ℕ := 2^65+2
def initializeCost : ℕ := NatAssign.Literals.cost (SignedBracket.ids base) initialWidth

theorem initialize_executes (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (fresh : ∀i∈SignedBracket.ids base,RationalAccumulator.Blank s.val i)
    (scratch : NatAssign.Scratch s.val) :
    ∃steps t,Executes input tape initializeCode steps s t ∧ steps≤ initializeCost ∧
      NatAssign.Bank (SignedBracket.ids base) (initial edgeInitial) t.val ∧
      NatAssign.Scratch t.val ∧
      (∀i∈SignedBracket.ids base,(initial edgeInitial i).bits.length≤ initialWidth) ∧
      BinaryPrecision.Frame ({0,1,2,3}∪SignedBracket.ids base) s.val t.val := by
  have width : ∀i∈SignedBracket.ids base,(initial edgeInitial i).bits.length≤ initialWidth := by
    have h:=initial_width edgeInitial (2^64) edgeInitial_endpoint_width.1 edgeInitial_endpoint_width.2
    simpa only [initialWidth,show 2*2^64+2=2^65+2 by norm_num] using h
  obtain ⟨c,t,e,charge,bank,blank,frame⟩:=NatAssign.Literals.fresh_executes
    (SignedBracket.ids base) (SignedBracket.ids_lower base (by decide)) (initial edgeInitial)
    initialWidth width input tape s fresh scratch
  exact ⟨c,t,e,charge,bank,blank,width,frame⟩

#print axioms initialize_executes
end Maxwell.Continuum.Calibration.EdgeBracketMachine
