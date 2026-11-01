import Maxwell.Continuum.CalibrationRootParameterMachine

/-! The root-table allocator's width words are computed by charged scans of
the actual grid count and retained rational scale. No width certificate is
supplied as an uncomputed runtime input. -/
namespace Maxwell.Continuum.Calibration.RootStorageWidths
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
open RationalAccumulator (Blank)
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def ids : Finset ℕ := RootParameters.ids∪{1027,1028,1029}
def changed : Finset ℕ := {0,1,2,3,345,346,348,349}
def prepare : List NatAssign.Instruction :=
  [.copy 331 348,.multiply 331 348,.multiply 331 348,.literal 349 2,.multiply 349 348,
   .literal 345 0,.literal 346 0,.literal 349 0]
def combine : List NatAssign.Instruction := [.add 349 346,.literal 349 0]
def finish : List NatAssign.Instruction :=
  [.add 349 346,.literal 349 1,.add 349 346,.literal 349 2,.add 349 345]
def prepared (v : ℕ→ℕ) := NatAssign.values prepare v
def counted (v : ℕ→ℕ) := Function.update (prepared v) 345 (2*(v 331)^3).bits.length
def positive (v : ℕ→ℕ) := Function.update (counted v) 346 (v 1027).bits.length
def negative (v : ℕ→ℕ) := Function.update (positive v) 349 (v 1028).bits.length
def combined (v : ℕ→ℕ) := NatAssign.values combine (negative v)
def denominator (v : ℕ→ℕ) := Function.update (combined v) 349 (v 1029).bits.length
def values (v : ℕ→ℕ) := NatAssign.values finish (denominator v)
def code : Code := .seq (NatAssign.code prepare)
  (.seq (WordLength.code 348 345) (.seq (WordLength.code 1027 346)
    (.seq (WordLength.code 1028 349) (.seq (NatAssign.code combine)
      (.seq (WordLength.code 1029 349) (NatAssign.code finish))))))
def firstWidth (B : ℕ) : ℕ := 2^8*(B+1)
def secondWidth (B : ℕ) : ℕ := 2^2*(firstWidth B+1)
def outputWidth (B : ℕ) : ℕ := 2^5*(secondWidth B+1)
def scanCost (B : ℕ) : ℕ := 48*(B+1)^2+1
def costBound (B : ℕ) : ℕ := stageCost B+3*scanCost (firstWidth B)+
  stageCost (firstWidth B)+scanCost (secondWidth B)+stageCost (secondWidth B)

theorem plans_valid (p : List NatAssign.Instruction)
    (hp : p=prepare ∨ p=combine ∨ p=finish) : ∀a∈p,a.Valid ids := by
  rcases hp with rfl|rfl|rfl <;>
    simp [prepare,combine,finish,NatAssign.Instruction.Valid,ids,RootParameters.ids]

theorem plans_changed (p : List NatAssign.Instruction)
    (hp : p=prepare ∨ p=combine ∨ p=finish) : NatAssign.changes p⊆changed := by
  rcases hp with rfl|rfl|rfl <;> decide

theorem prepared_count (v : ℕ→ℕ) : prepared v 348=2*(v 331)^3 := by
  simp [prepared,prepare,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]
  ring

theorem outputs (v : ℕ→ℕ) :
    values v 345=(2*(v 331)^3).bits.length+2 ∧
    values v 346=(v 1027).bits.length+(v 1028).bits.length+(v 1029).bits.length+1 := by
  simp [values,finish,denominator,combined,combine,negative,positive,counted,
    NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value]
  omega

theorem values_keep (v : ℕ→ℕ) (i : ℕ) (hi : i≠345 ∧ i≠346 ∧ i≠348 ∧ i≠349) :
    values v i=v i := by
  rcases hi with ⟨h0,h1,h2,h3⟩
  simp [values,finish,denominator,combined,combine,negative,positive,counted,prepared,prepare,
    NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    Function.update_of_ne,h0,h1,h2,h3]

theorem natural_bounds (v : ℕ→ℕ) :
    2≤values v 345 ∧ (v 331).bits.length≤values v 345 ∧
    (2*(v 331)^3).bits.length≤values v 345 := by
  have grid_le : v 331≤2*(v 331)^3 := by
    have h := Nat.le_self_pow (by decide : 3≠0) (v 331)
    omega
  have bits_le := RationalWords.bits_mono grid_le
  rw [(outputs v).1]
  omega

theorem scale_bounds (v : ℕ→ℕ) (scale : Parts)
    (hp : v 1027=scale.positive) (hn : v 1028=scale.negative)
    (hd : v 1029=scale.denominator) : 1≤values v 346 ∧ scale.Width (values v 346) := by
  rw [(outputs v).2,hp,hn,hd]
  unfold Parts.Width
  omega

private theorem bits_length_le (n : ℕ) : n.bits.length≤n := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  exact Nat.lt_two_pow_self

private theorem update_width (v : ℕ→ℕ) (B target value : ℕ)
    (hw : ∀i∈ids,(v i).bits.length≤B) (hvalue : value.bits.length≤B) :
    ∀i∈ids,((Function.update v target value) i).bits.length≤B := by
  intro i hi
  by_cases h : i=target
  · simpa only [h,Function.update_self] using hvalue
  · simpa only [Function.update_of_ne h] using hw i hi

private theorem stage (plan : List NatAssign.Instruction)
    (valid : ∀a∈plan,a.Valid ids) (hlen : plan.length≤25)
    (v : ℕ→ℕ) (B : ℕ) (hw : ∀i∈ids,(v i).bits.length≤B)
    (hl : ∀a∈plan,a.literalWidth≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape (NatAssign.code plan) cost s t ∧ cost≤stageCost B ∧
      NatAssign.Bank ids (NatAssign.values plan v) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame (NatAssign.changes plan) s.val t.val := by
  have lower : ∀i∈ids,4 ≤ i := by decide
  obtain ⟨c,t,e,hc,b,z,f⟩ := NatAssign.executes ids lower plan valid v input tape s hb hz
  have price := NatAssign.price_bound ids plan valid v B hw hl
  have factor : 3000*8^plan.length≤(2:ℕ)^96 := by
    have p := Nat.pow_le_pow_right (by decide : 1≤8) hlen
    norm_num at p ⊢
    omega
  exact ⟨c,t,e,hc.trans (price.trans (Nat.mul_le_mul_right _ factor)),b,z,f⟩

theorem executes (v : ℕ→ℕ) (B : ℕ) (hB : 2≤B)
    (hw : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤costBound B ∧
      NatAssign.Bank ids (values v) t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈ids,(values v i).bits.length≤outputWidth B) ∧
      BinaryPrecision.Frame changed s.val t.val := by
  have pl : ∀a∈prepare,a.literalWidth≤B := by
    simp [prepare,NatAssign.Instruction.literalWidth,show (2:ℕ).bits.length=2 by rfl]
    omega
  have pw : ∀i∈ids,(prepared v i).bits.length≤firstWidth B := by
    intro i hi
    have h := NatAssign.values_width_bound ids prepare (plans_valid _ (Or.inl rfl)) v B hw pl i hi
    simpa only [prepared,firstWidth,show prepare.length=8 by rfl] using (Nat.le_add_right _ _).trans h
  obtain ⟨c0,s0,e0,hc0,b0,z0,f0⟩ := stage prepare (plans_valid _ (Or.inl rfl)) (by decide)
    v B hw pl input tape s hb hz
  obtain ⟨c1,s1,e1,hc1,b1,z1,f1⟩ := NatAssign.stored_length ids 348 345 (by decide)
    (by decide) (by decide) (by decide) (prepared v) (by
      simp [prepared,prepare,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value])
    input tape s0 b0 z0
  rw [prepared_count] at b1 hc1
  change NatAssign.Bank ids (counted v) s1.val at b1
  have w1 : ∀i∈ids,(counted v i).bits.length≤firstWidth B :=
    update_width _ _ _ _ pw ((bits_length_le _).trans (by simpa only [prepared_count] using pw 348 (by decide)))
  obtain ⟨c2,s2,e2,hc2,b2,z2,f2⟩ := NatAssign.stored_length ids 1027 346 (by decide)
    (by decide) (by decide) (by decide) (counted v) (by
      simp [counted,prepared,prepare,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value])
    input tape s1 b1 z1
  have cpos : counted v 1027=v 1027 := by
    simp [counted,prepared,prepare,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target]
  rw [cpos] at b2 hc2
  change NatAssign.Bank ids (positive v) s2.val at b2
  have w2 := update_width (counted v) (firstWidth B) 346 (v 1027).bits.length w1
    ((bits_length_le _).trans (by rw [←cpos];exact w1 1027 (by decide)))
  obtain ⟨c3,s3,e3,hc3,b3,z3,f3⟩ := NatAssign.stored_length ids 1028 349 (by decide)
    (by decide) (by decide) (by decide) (positive v) (by
      simp [positive,counted,prepared,prepare,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value])
    input tape s2 b2 z2
  have cneg : positive v 1028=v 1028 := by
    simp [positive,counted,prepared,prepare,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target]
  rw [cneg] at b3 hc3
  change NatAssign.Bank ids (negative v) s3.val at b3
  have w3 := update_width (positive v) (firstWidth B) 349 (v 1028).bits.length w2
    ((bits_length_le _).trans (by rw [←cneg];exact w2 1028 (by decide)))
  have cl : ∀a∈combine,a.literalWidth≤firstWidth B := by simp [combine,NatAssign.Instruction.literalWidth]
  have cw : ∀i∈ids,(combined v i).bits.length≤secondWidth B := by
    intro i hi
    have h := NatAssign.values_width_bound ids combine (plans_valid _ (Or.inr (Or.inl rfl)))
      (negative v) (firstWidth B) w3 cl i hi
    simpa only [combined,secondWidth,show combine.length=2 by rfl] using (Nat.le_add_right _ _).trans h
  obtain ⟨c4,s4,e4,hc4,b4,z4,f4⟩ := stage combine (plans_valid _ (Or.inr (Or.inl rfl)))
    (by decide) (negative v) (firstWidth B) w3 cl input tape s3 b3 z3
  obtain ⟨c5,s5,e5,hc5,b5,z5,f5⟩ := NatAssign.stored_length ids 1029 349 (by decide)
    (by decide) (by decide) (by decide) (combined v) (by
      simp [combined,combine,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value])
    input tape s4 b4 z4
  have cden : combined v 1029=v 1029 := by
    simp [combined,combine,negative,positive,counted,prepared,prepare,NatAssign.values,
      NatAssign.Instruction.update,NatAssign.Instruction.target]
  rw [cden] at b5 hc5
  change NatAssign.Bank ids (denominator v) s5.val at b5
  have w5 := update_width (combined v) (secondWidth B) 349 (v 1029).bits.length cw
    ((bits_length_le _).trans (by rw [←cden];exact cw 1029 (by decide)))
  have fl : ∀a∈finish,a.literalWidth≤secondWidth B := by
    simp [finish,NatAssign.Instruction.literalWidth,secondWidth,firstWidth,show (2:ℕ).bits.length=2 by rfl]
    omega
  have fw : ∀i∈ids,(values v i).bits.length≤outputWidth B := by
    intro i hi
    have h := NatAssign.values_width_bound ids finish (plans_valid _ (Or.inr (Or.inr rfl)))
      (denominator v) (secondWidth B) w5 fl i hi
    simpa only [values,outputWidth,show finish.length=5 by rfl] using (Nat.le_add_right _ _).trans h
  obtain ⟨c6,t,e6,hc6,b6,z6,f6⟩ := stage finish (plans_valid _ (Or.inr (Or.inr rfl)))
    (by decide) (denominator v) (secondWidth B) w5 fl input tape s5 b5 z5
  refine ⟨c0+(c1+(c2+(c3+(c4+(c5+c6))))),t,
    e0.seq (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))),?_,b6,z6,fw,?_⟩
  · have k1 := pw 348 (by decide)
    rw [prepared_count] at k1
    have k2 : (v 1027).bits.length≤firstWidth B := by rw [←cpos];exact w1 1027 (by decide)
    have k3 : (v 1028).bits.length≤firstWidth B := by rw [←cneg];exact w2 1028 (by decide)
    have k5 : (v 1029).bits.length≤secondWidth B := by rw [←cden];exact cw 1029 (by decide)
    have p1 := Nat.pow_le_pow_left (Nat.add_le_add_right k1 1) 2
    have p2 := Nat.pow_le_pow_left (Nat.add_le_add_right k2 1) 2
    have p3 := Nat.pow_le_pow_left (Nat.add_le_add_right k3 1) 2
    have p5 := Nat.pow_le_pow_left (Nat.add_le_add_right k5 1) 2
    unfold costBound scanCost
    omega
  · exact (f0.mono (plans_changed _ (Or.inl rfl))).trans
      ((f1.mono (by decide)).trans ((f2.mono (by decide)).trans ((f3.mono (by decide)).trans
        ((f4.mono (plans_changed _ (Or.inr (Or.inl rfl)))).trans ((f5.mono (by decide)).trans
          (f6.mono (plans_changed _ (Or.inr (Or.inr rfl)))))))))

#print axioms executes
#print axioms natural_bounds
#print axioms scale_bounds
end Maxwell.Continuum.Calibration.RootStorageWidths
