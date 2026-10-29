import Maxwell.Cost.Structured.NatAssign
import Maxwell.Cost.RationalAccumulator.Move

namespace Maxwell.Cost.CalibrationMatrix.GeneratedMetadata
open Structured
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 1800000

def plan : List NatAssign.Instruction :=
  [.literal 128 2,.copy 120 121,.multiply 128 121,
   .literal 128 1,.add 128 121,.copy 121 122,
   .multiply 121 122,.multiply 121 122,.literal 128 3,.multiply 128 122,
   .copy 122 136,.multiply 122 136,.literal 128 0,
   .literal 129 3,.literal 130 31,.literal 131 20]

def ids : Finset ℕ := {120,121,122,128,129,130,131,136}

def initial (R : ℕ) (i : ℕ) : ℕ := if i = 120 then R else 0

def code : Code := NatAssign.code plan

def costCap (R : ℕ) : ℕ := NatAssign.price plan (initial R)

theorem bit_bounds (R : ℕ) :
    (2*R+1).bits.length ≤ R.bits.length+3 ∧
    (3*(2*R+1)^3).bits.length ≤ 3*R.bits.length+11 ∧
    ((3*(2*R+1)^3)^2).bits.length ≤ 6*R.bits.length+22 := by
  have h2 := RationalAccumulator.bits_mul_le 2 R
  have hplus := RationalAccumulator.bits_add_le (2*R) 1
  have hsquare := RationalAccumulator.bits_mul_le (2*R+1) (2*R+1)
  have hcube := RationalAccumulator.bits_mul_le (2*R+1) ((2*R+1)*(2*R+1))
  have hdim := RationalAccumulator.bits_mul_le 3 ((2*R+1)*((2*R+1)*(2*R+1)))
  have hcount := RationalAccumulator.bits_mul_le (3*(2*R+1)^3) (3*(2*R+1)^3)
  norm_num only [show (2 : ℕ).bits.length = 2 from rfl,
    show (1 : ℕ).bits.length = 1 from rfl,show (3 : ℕ).bits.length = 2 from rfl] at h2 hplus hdim
  have hpow : (2*R+1)*((2*R+1)*(2*R+1)) = (2*R+1)^3 := by ring
  rw [hpow] at hcube hdim
  rw [← pow_two] at hcount
  omega

theorem comparison_bound (R : ℕ) :
    (2*R+1).bits.length+(3*(2*R+1)^3).bits.length+
      ((3*(2*R+1)^3)^2).bits.length+1 ≤ 10*R.bits.length+37 := by
  obtain ⟨hw,hn,hcount⟩ := bit_bounds R
  omega

theorem costCap_le (R : ℕ) : costCap R ≤ 2000000*(R.bits.length+5)^2 := by
  let L := 1+2*R
  have h2 : (2*R).bits.length ≤ R.bits.length+2 := by
    simpa only [show (2 : ℕ).bits.length = 2 from rfl,Nat.add_comm] using
      RationalAccumulator.bits_mul_le 2 R
  have hL : L.bits.length ≤ R.bits.length+3 := by
    simpa only [L,Nat.add_comm] using (bit_bounds R).1
  have hLL := RationalAccumulator.bits_mul_le L L
  have hLLL := RationalAccumulator.bits_mul_le L (L*L)
  have hdim := RationalAccumulator.bits_mul_le 3 (L*(L*L))
  simp only [show (3 : ℕ).bits.length = 2 from rfl] at hdim
  have hq1 : (R.bits.length+5)^2 ≤ (6*R.bits.length+25)^2 := Nat.pow_le_pow_left (by omega) 2
  have hq2 : (L.bits.length+L.bits.length+3)^2 ≤ (6*R.bits.length+25)^2 := Nat.pow_le_pow_left (by omega) 2
  have hq3 : (L.bits.length+(L*L).bits.length+3)^2 ≤ (6*R.bits.length+25)^2 := Nat.pow_le_pow_left (by omega) 2
  have hq4 : (2+(L*(L*L)).bits.length+3)^2 ≤ (6*R.bits.length+25)^2 := Nat.pow_le_pow_left (by omega) 2
  have hq5 : ((3*(L*(L*L))).bits.length+(3*(L*(L*L))).bits.length+3)^2 ≤
      (6*R.bits.length+25)^2 := Nat.pow_le_pow_left (by omega) 2
  have hcost : costCap R ≤ 3000*(6*R.bits.length+25)^2+300*R.bits.length+3000 := by
    simp [costCap,plan,NatAssign.price,NatAssign.Instruction.price,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,initial]
    norm_num only [show (2 : ℕ).bits.length = 2 from rfl,show (3 : ℕ).bits.length = 2 from rfl,
      show (31 : ℕ).bits.length = 5 from rfl,show (20 : ℕ).bits.length = 5 from rfl]
    dsimp [L] at hL hLL hLLL hdim hq2 hq3 hq4 hq5
    nlinarith only [h2,hL,hLL,hLLL,hdim,hq1,hq2,hq3,hq4,hq5]
  nlinarith only [hcost,Nat.zero_le (R.bits.length^2),Nat.zero_le R.bits.length]

theorem values (R : ℕ) :
    NatAssign.values plan (initial R) 121 = 2*R+1 ∧
    NatAssign.values plan (initial R) 122 = 3*(2*R+1)^3 ∧
    NatAssign.values plan (initial R) 136 = (3*(2*R+1)^3)^2 ∧
    NatAssign.values plan (initial R) 128 = 0 ∧
    NatAssign.values plan (initial R) 129 = 3 ∧
    NatAssign.values plan (initial R) 130 = 31 ∧
    NatAssign.values plan (initial R) 131 = 20 := by
  simp [plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,initial,pow_succ,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc,Nat.add_comm]

/-- Cube width, dimension and traversal count are computed by actual
binary additions and products. The three fixed auxiliary words are emitted
by literal-writing code, and the arithmetic temporary is reclaimed. -/
theorem executes (input : List Bool) (tape : ℕ → Bool) (R : ℕ) (s : Store)
    (hR : Word s.val 120 R) (hz : ∀ i ∈ ids, i ≠ 120 → Word s.val i 0)
    (hscratch : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape code cost s t ∧ cost ≤ costCap R ∧
      Word t.val 121 (2*R+1) ∧ Word t.val 122 (3*(2*R+1)^3) ∧
      Word t.val 136 ((3*(2*R+1)^3)^2) ∧ Word t.val 128 0 ∧
      Word t.val 129 3 ∧ Word t.val 130 31 ∧ Word t.val 131 20 ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame (NatAssign.changes plan) s.val t.val := by
  have valid : ∀ a ∈ plan, a.Valid ids := by
    simp [plan,NatAssign.Instruction.Valid,ids]
  have hids : ∀ i ∈ ids, 4 ≤ i := by
    intro i hi
    simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  have hb : NatAssign.Bank ids (initial R) s.val := by
    intro i hi
    by_cases he : i = 120
    · subst i; simpa [initial] using hR
    · simpa [initial,he] using hz i hi he
  obtain ⟨cost,t,he,hc,hb,hs,hf⟩ := NatAssign.executes ids hids plan valid (initial R) input tape s hb hscratch
  obtain ⟨h121,h122,h136,h128,h129,h130,h131⟩ := values R
  exact ⟨cost,t,he,hc,by simpa only [h121] using hb 121 (by decide),
    by simpa only [h122] using hb 122 (by decide),by simpa only [h136] using hb 136 (by decide),
    by simpa only [h128] using hb 128 (by decide),by simpa only [h129] using hb 129 (by decide),
    by simpa only [h130] using hb 130 (by decide),by simpa only [h131] using hb 131 (by decide),hs,hf⟩

theorem preserved {s t : BitRAMState} (h : BinaryPrecision.Frame (NatAssign.changes plan) s t)
    (i : ℕ) (hi : i = 120 ∨ i = 100 ∨ i = 101 ∨ i = 110 ∨ i = 111 ∨ 230 ≤ i) :
    t.tapes i = s.tapes i := by
  apply h.tapes
  simp [NatAssign.changes,plan,NatAssign.Instruction.target]
  omega

theorem compiled_run (input : List Bool) (tape : ℕ → Bool) (R : ℕ) (s : Store)
    (hR : Word s.val 120 R) (hz : ∀ i ∈ ids, i ≠ 120 → Word s.val i 0)
    (hscratch : NatAssign.Scratch s.val) :
    ∃ t : Store,
      (runPriced (code.compile.next input tape) (costCap R+1) s.val).finished = some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (costCap R+1) s.val).instructions ≤
        2000000*(R.bits.length+5)^2 ∧
      Word t.val 121 (2*R+1) ∧ Word t.val 122 (3*(2*R+1)^3) ∧
      Word t.val 136 ((3*(2*R+1)^3)^2) ∧ Word t.val 128 0 ∧
      Word t.val 129 3 ∧ Word t.val 130 31 ∧ Word t.val 131 20 ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame (NatAssign.changes plan) s.val t.val := by
  obtain ⟨cost,t,he,hc,ht⟩ := executes input tape R s hR hz hscratch
  have hr := he.compiled_run (costCap R+1) (by omega)
  exact ⟨t,hr.1,hr.2 ▸ hc.trans (costCap_le R),ht⟩

end Maxwell.Cost.CalibrationMatrix.GeneratedMetadata
