import Maxwell.Cost.NormalizeRatio.Correctness
import Maxwell.Cost.Structured.NatAssign.Bounds
import Maxwell.Cost.Structured.RegisterFootprint

namespace Maxwell.Cost.WeightedSource.Round
open Structured RationalAccumulator
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def plan : List NatAssign.Instruction :=
  [.copy 350 30,.multiply 410 30,.copy 351 31,.multiply 411 31,
   .literal 32 1,.literal 33 1,.copy 412 34]

def cleanup : List NatAssign.Instruction :=
  [.literal 30 0,.literal 31 0,.literal 32 0,.literal 33 0,.literal 34 0]

def ids : Finset ℕ := {30,31,32,33,34,35,36,350,351,410,411,412}

def initial (m d a q power : ℕ) (i : ℕ) : ℕ :=
  if i=350 then m else if i=351 then d else if i=410 then a else
  if i=411 then q else if i=412 then power else 0

def prepared (m d a q power : ℕ) := NatAssign.values plan (initial m d a q power)

def changed : Finset ℕ := {0,1,2,3,4,30,31,32,33,34,35,36}

def code : Code := .seq (NatAssign.code plan)
  (.seq (Code.atom (.bitAnd 35 358 358))
    (.seq NormalizeRatio.code (NatAssign.code cleanup)))

def value (negative : Bool) (m d a q : ℕ) : ℚ :=
  (if negative then -((a*m : ℕ) : ℚ) else ((a*m : ℕ) : ℚ)) / ((q*d : ℕ) : ℚ)

private theorem plan_valid : ∀ op ∈ plan, op.Valid ids := by
  simp [plan,NatAssign.Instruction.Valid,ids]
private theorem cleanup_valid : ∀ op ∈ cleanup, op.Valid ids := by
  simp [cleanup,NatAssign.Instruction.Valid,ids]
private theorem ids_ge : ∀ i ∈ ids, 4 ≤ i := by
  simp only [ids,Finset.mem_insert,Finset.mem_singleton]
  omega

private theorem scratch_iff (s : BitRAMState) : NatAssign.Scratch s ↔ Scratch s 0 := by
  constructor
  · intro h
    exact ⟨h 0 (by omega),(zero_word_iff_blank s 1).mpr (h 1 (by omega)),
      h 2 (by omega),h 3 (by omega)⟩
  · intro h i hi
    interval_cases i
    · exact h.1
    · exact (zero_word_iff_blank s 1).mp h.2.1
    · exact h.2.2.1
    · exact h.2.2.2

private theorem normalized_prepared (negative : Bool) (m d a q power : ℕ) :
    NormalizeRatio.normalized (prepared m d a q power) negative = value negative m d a q := by
  cases negative <;> simp [NormalizeRatio.normalized,prepared,NatAssign.values,plan,
    NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
    initial,value]

/-- The weighted numerator, common denominator, scaled division, nearest
rounding and arithmetic cleanup are all executed by the same finite code.
The weight numerator may be zero. -/
theorem executes (input : List Bool) (tape : ℕ → Bool) (m d a q p B : ℕ)
    (negative : Bool) (hd : 0<d) (hq : 0<q) (hB : 1≤B)
    (hm : m.bits.length≤B) (hdb : d.bits.length≤B) (ha : a.bits.length≤B)
    (hqb : q.bits.length≤B) (hp : (2^p : ℕ).bits.length≤B)
    (s : Store) (hb : Bank s.val (fun _ => 0)) (hs : Scratch s.val 0)
    (h4 : Blank s.val 4) (h350 : Word s.val 350 m) (h351 : Word s.val 351 d)
    (h410 : Word s.val 410 a) (h411 : Word s.val 411 q) (h412 : Word s.val 412 (2^p))
    (hnegative : s.val.registers 358=negative) :
    ∃ cost, ∃ t : Store, cost≤100000000000*(B+2)^2 ∧
      Executes input tape code cost s t ∧
      SignedRound.Output t.val (Logical.Rounding.nearest p (value negative m d a q)).numerator ∧
      Bank t.val (fun _ => 0) ∧ Scratch t.val 0 ∧
      BinaryPrecision.Frame changed s.val t.val ∧ t.val.registers 358=negative := by
  let v := initial m d a q (2^p)
  have hv : NatAssign.Bank ids v s.val := by
    intro i hi
    simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [v,initial,↓reduceIte]
    all_goals first | exact h350 | exact h351 | exact h410 | exact h411 | exact h412 | exact hb _ (by omega) (by omega)
  have hvbits : ∀ i ∈ ids, (v i).bits.length≤B := by
    intro i _
    simp only [v,initial]
    split_ifs <;> first | assumption | simp
  obtain ⟨c1,t1,e1,hc1,b1,s1,f1⟩ := NatAssign.executes ids ids_ge plan plan_valid v input tape s hv ((scratch_iff _).mpr hs)
  have hprice1 := NatAssign.price_bound ids plan plan_valid v B hvbits (by
    intro op hop
    simp only [plan,List.mem_cons,List.not_mem_nil,or_false] at hop
    rcases hop with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [NatAssign.Instruction.literalWidth] <;> omega)
  have hbound1 : c1≤3000*8^7*(B+2)^2 := by
    have hh := hc1.trans hprice1
    simpa [plan] using hh
  have b1' : Bank t1.val (prepared m d a q (2^p)) := by
    intro i hi hj
    exact b1 i (by interval_cases i <;> decide)
  have prepared_bits : ∀ i : ℕ, 30 ≤ i → i ≤ 34 →
      ((prepared m d a q (2^p)) i).bits.length≤2*B+1 := by
    intro i hi hj
    have hprod1 := bits_mul_le a m
    have hprod2 := bits_mul_le q d
    interval_cases i <;>
      simp [prepared,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
        NatAssign.Instruction.value,initial] <;> omega
  let t2 := Store.ofState (t1.val.setRegister 35 (t1.val.registers 358 && t1.val.registers 358))
  have e2 := Executes.bitAnd input tape t1 35 358 358
  have sign2 : t2.val.registers 35=negative := by
    have he := e1.protectsRegister 358 (by decide)
    simp [t2,Store.ofState,BitRAMState.setRegister,he,hnegative]
  obtain ⟨c3,t3,hc3,e3,out3,b3,s3,f3⟩ := NormalizeRatio.normalizes input tape
    (prepared m d a q (2^p)) (2*B+1) p negative prepared_bits
    (by simpa [prepared,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,initial] using Nat.mul_pos hq hd)
    (by simp [prepared,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,initial])
    (by simp [prepared,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,initial])
    (by simp [prepared,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,initial])
    (by simp [prepared,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,initial])
    (by simp [prepared,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,initial])
    t2 b1' ((scratch_iff _).mp s1)
    (blank_of_eq (f1.tapes 4 (by decide)) h4) sign2
  have f3' : BinaryPrecision.Frame changed t1.val t3.val := by
    refine ⟨f3.1,f3.2.1,f3.2.2.1,f3.2.2.2.1,f3.2.2.2.2.1,?_⟩
    intro i hi
    simp only [changed,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
    exact f3.2.2.2.2.2.1 i (by omega) (by omega)
  have b3' : NatAssign.Bank ids (prepared m d a q (2^p)) t3.val := by
    intro i hi
    by_cases hi' : i≤36
    · exact b3 i (by have := ids_ge i hi; simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi; omega) hi'
    · exact word_of_eq (f3'.tapes i (by simp only [changed,Finset.mem_insert,Finset.mem_singleton]; omega)) (b1 i hi)
  obtain ⟨c4,t4,e4,hc4,b4,s4,f4⟩ := NatAssign.executes ids ids_ge cleanup cleanup_valid
    (prepared m d a q (2^p)) input tape t3 b3' ((scratch_iff _).mpr s3)
  have hbitsall : ∀ i∈ids, ((prepared m d a q (2^p)) i).bits.length≤2*B+1 := by
    intro i hi
    by_cases hlow : i≤34
    · exact prepared_bits i (by simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi; omega) hlow
    · simp only [prepared,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
        NatAssign.Instruction.value]
      simp only [Function.update_apply]
      split_ifs <;> try omega
      exact (hvbits i hi).trans (by omega)
  have hprice4 := NatAssign.price_bound ids cleanup cleanup_valid
    (prepared m d a q (2^p)) (2*B+1) hbitsall (by
      intro op hop
      simp only [cleanup,List.mem_cons,List.not_mem_nil,or_false] at hop
      rcases hop with rfl|rfl|rfl|rfl|rfl <;> simp [NatAssign.Instruction.literalWidth])
  have hbound4 : c4≤3000*8^5*(2*B+3)^2 := by
    have hh := hc4.trans hprice4
    simpa [cleanup,Nat.add_assoc] using hh
  refine ⟨c1+(2+(c3+c4)),t4,?_,e1.seq (e2.seq (e3.seq e4)),?_,?_,
    (scratch_iff _).mp s4,?_,?_⟩
  · nlinarith
  · obtain ⟨origin,ho,hsg⟩ := out3
    rw [normalized_prepared] at ho hsg
    exact ⟨origin,(f4.tapes 4 (by decide)).trans ho,
      (e4.protectsRegister 23 (by decide)).trans hsg⟩
  · intro i hi hj
    have hh := b4 i (by interval_cases i <;> decide)
    interval_cases i <;>
      simpa [cleanup,prepared,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
        NatAssign.Instruction.value,initial] using hh
  · exact ((f1.mono (by decide)).trans f3').trans (f4.mono (by decide))
  · exact ((e4.protectsRegister 358 (by decide)).trans
      ((e3.protectsRegister 358 (by decide)).trans (by
        simpa [t2,Store.ofState,BitRAMState.setRegister] using (e1.protectsRegister 358 (by decide))))).trans hnegative

end Maxwell.Cost.WeightedSource.Round
