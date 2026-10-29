import Maxwell.Cost.Structured.NatAssign.Bounds

/-! Exact source-seed cross multiplication from runtime rational words.
No reduced fraction, precomputed seed vector, or rounded RHS is supplied. -/
namespace Maxwell.Cost.PhysicalSource.SeedArithmetic
open Structured RationalAccumulator
set_option maxHeartbeats 1500000

def ids : Finset ℕ := {334,335,336,360,361,362,363,364,365,366,367,368,369,506,507}

def instructions : List NatAssign.Instruction :=
  [.copy 362 334,.multiply 366 334,.copy 363 368,.multiply 367 368,.add 368 334,
   .multiply 507 334,.literal 369 4,.multiply 369 334,
   .copy 363 335,.multiply 366 335,.copy 362 368,.multiply 367 368,.add 368 335,
   .multiply 507 335,.multiply 369 335,
   .copy 361 336,.multiply 364 336,.multiply 365 336,.multiply 506 336]

def code : Code := NatAssign.code instructions

def positive (v : ℕ→ℕ) : ℕ := 4*v 507*(v 366*v 362+v 367*v 363)
def negative (v : ℕ→ℕ) : ℕ := 4*v 507*(v 366*v 363+v 367*v 362)
def denominator (v : ℕ→ℕ) : ℕ := v 361*v 364*v 365*v 506

def value (v : ℕ→ℕ) : ℚ :=
  (4/(v 365:ℚ)) * (((v 362:ℚ)-v 363)/v 364) *
    ((((v 366:ℚ)-v 367)/v 361)/((v 506:ℚ)/v 507))

theorem fraction_value (v : ℕ→ℕ) :
    ((positive v:ℚ)-negative v)/denominator v = value v := by
  simp only [positive,negative,denominator,value,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,
    div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

theorem denominator_pos (v : ℕ→ℕ)
    (h : 0<v 361 ∧ 0<v 364 ∧ 0<v 365 ∧ 0<v 506) : 0<denominator v := by
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos h.1 h.2.1) h.2.2.1) h.2.2.2

theorem values_positive (v : ℕ→ℕ) : NatAssign.values instructions v 334 = positive v := by
  simp [instructions,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,Function.update,positive]
  ring

theorem values_negative (v : ℕ→ℕ) : NatAssign.values instructions v 335 = negative v := by
  simp [instructions,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,Function.update,negative]
  ring

theorem values_denominator (v : ℕ→ℕ) : NatAssign.values instructions v 336 = denominator v := by
  simp [instructions,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,Function.update,denominator]
  ring

theorem valid : ∀ a ∈ instructions, a.Valid ids := by
  intro a ha
  simp [instructions] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [NatAssign.Instruction.Valid,ids]

/-- A fixed finite list of integer products computes all three seed fields.
Its only width parameter bounds actual stored operands, and all costs are
charged by the already checked bit arithmetic. -/
theorem executes (v : ℕ→ℕ) (B : ℕ) (hB : 3≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hr : NatAssign.Scratch s.val)
    (hv : ∀ i ∈ ids, (v i).bits.length≤B) :
    ∃ cost t, cost≤3000*8^19*(B+2)^2 ∧ Executes input tape code cost s t ∧
      Word t.val 334 (positive v) ∧ Word t.val 335 (negative v) ∧
      Word t.val 336 (denominator v) ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame {0,1,2,3,334,335,336,368,369} s.val t.val := by
  obtain ⟨c,t,he,hc,ht,hs,hf⟩ := NatAssign.executes ids
    (by intro i hi; simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi; omega)
    instructions valid v input tape s hb hr
  refine ⟨c,t,?_,he,by simpa only [values_positive] using ht 334 (by decide),
    by simpa only [values_negative] using ht 335 (by decide),
    by simpa only [values_denominator] using ht 336 (by decide),hs,?_⟩
  · have hl : ∀ a ∈ instructions, a.literalWidth≤B := by
      intro a ha
      simp [instructions] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        first | exact Nat.zero_le _ | exact hB
    exact hc.trans (by simpa only [instructions,List.length_cons,List.length_nil] using
      NatAssign.price_bound ids instructions valid v B hv hl)
  · have hh : NatAssign.changes instructions = {0,1,2,3,334,335,336,368,369} := by decide
    rw [hh] at hf
    exact hf

end Maxwell.Cost.PhysicalSource.SeedArithmetic
