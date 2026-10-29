import Maxwell.Cost.RealLink
import Mathlib.Data.Nat.Size

/-! The simulator uses ordinary natural index words. Banks are interleaved,
so an unbounded output cannot overwrite a simulated tape. Dead address-stack
cells are deliberately unconstrained; the serializer may use them as scratch.
The head center is a charged caller-supplied cap, not a real-to-natural cast. -/
namespace Maxwell.Cost.RealSimulation

structure Layout where
  registerCount : ℕ
  tapeCount : ℕ

def Layout.stride (L : Layout) : ℕ := L.tapeCount + 4
def Layout.bitRegister (_L : Layout) (r : ℕ) : ℕ := 256 + r
def Layout.tapeHead (L : Layout) (t : ℕ) : ℕ := 256 + L.registerCount + t
def Layout.frameEnd (L : Layout) : ℕ := 256 + L.registerCount + L.tapeCount
def Layout.inputBank (L : Layout) : ℕ := L.tapeCount + 2
def Layout.outputBank (L : Layout) : ℕ := L.tapeCount + 3

def virtualPC : ℕ := 20
def addressLength : ℕ := 21
def inputHead : ℕ := 22
def inputBase : ℕ := 128
def inputLength : ℕ := 129
def outputBase : ℕ := 130
def outputLength : ℕ := 131
def workspaceOrigin : ℕ := 132
def bankStride : ℕ := 133
def headCenter : ℕ := 134

def Layout.slot (L : Layout) (origin bank coordinate : ℕ) : ℕ :=
  origin + L.stride * coordinate + bank

@[simp] theorem Layout.stride_pos (L : Layout) : 0 < L.stride := by
  simp [stride]

theorem Layout.slot_injective (L : Layout) (origin bank bank' a a' : ℕ)
    (hb : bank < L.stride) (hb' : bank' < L.stride) :
    L.slot origin bank a = L.slot origin bank' a' ↔ bank = bank' ∧ a = a' := by
  constructor
  · intro h
    have he : L.stride * a + bank = L.stride * a' + bank' := by
      simpa only [slot, Nat.add_assoc, Nat.add_left_cancel_iff] using h
    have hm := congrArg (fun n => n % L.stride) he
    have hbank : bank = bank' := by
      simpa [Nat.add_mod, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb'] using hm
    subst bank'
    have hmul : L.stride * a = L.stride * a' := Nat.add_right_cancel he
    exact ⟨rfl, (Nat.mul_left_cancel L.stride_pos hmul)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem Layout.slot_ge_origin (L : Layout) (origin bank coordinate : ℕ) :
    origin ≤ L.slot origin bank coordinate := by
  unfold slot
  omega

theorem Layout.slot_ne (L : Layout) (origin bank bank' a a' : ℕ)
    (hb : bank < L.stride) (hb' : bank' < L.stride) (hne : bank ≠ bank') :
    L.slot origin bank a ≠ L.slot origin bank' a' := by
  intro h
  exact hne ((L.slot_injective origin bank bank' a a' hb hb').mp h).1

/-- A constant-width bank number adds only a fixed factor to word magnitude.
The caller separately proves the origin and logical coordinates fit its cap. -/
theorem Layout.slot_bound (L : Layout) (origin bank coordinate bound : ℕ)
    (ho : origin < bound) (hb : bank < L.stride) (hc : coordinate < bound) :
    L.slot origin bank coordinate < (L.stride + 1) * bound := by
  have h := Nat.mul_le_mul_left L.stride (show coordinate + 1 ≤ bound by omega)
  simp only [Nat.mul_add, Nat.mul_one] at h
  unfold slot
  nlinarith

def symbol : Option Bool → ℕ
  | none => 0
  | some b => b.toNat + 1

@[simp] theorem symbol_none : symbol none = 0 := rfl
@[simp] theorem symbol_some (b : Bool) : symbol (some b) = b.toNat + 1 := rfl
theorem symbol_getD (b : Option Bool) : symbol b - 1 = (b.getD false).toNat := by
  cases b with
  | none => rfl
  | some b => cases b <;> rfl
theorem symbol_present (b : Option Bool) : (decide (0 < symbol b)).toNat = b.isSome.toNat := by
  cases b with
  | none => rfl
  | some b => cases b <;> rfl

def centered (center : ℕ) (head : ℤ) : ℕ := (center + head).toNat

theorem centered_cast (center : ℕ) (head : ℤ) (h : -(center : ℤ) ≤ head) :
    (centered center head : ℤ) = center + head := by
  exact Int.toNat_of_nonneg (by omega)

theorem centered_right (center : ℕ) (head : ℤ) (h : -(center : ℤ) ≤ head) :
    centered center (head + 1) = centered center head + 1 := by
  have h1 := centered_cast center head h
  have h2 := centered_cast center (head + 1) (by omega)
  omega

theorem centered_left (center : ℕ) (head : ℤ) (h : -(center : ℤ) < head) :
    centered center (head - 1) = centered center head - 1 := by
  have h1 := centered_cast center head (by omega)
  have h2 := centered_cast center (head - 1) (by omega)
  omega

/-- The complete representation relation includes input and output buffers,
all live address bits, every represented Boolean register and every simulated
memory/tape cell. No assumption supplies the result of a simulated transition. -/
structure Represents (L : Layout) (origin center : ℕ) (bits : List Bool)
    (source : BitRAMState) (target : RAMState) : Prop where
  origin_above_frame : L.frameEnd ≤ origin
  pc : target.indices virtualPC = source.pc
  address_length : target.indices addressLength = source.address.length
  input_head : target.indices inputHead = centered center source.inputHead
  registers : ∀ r < L.registerCount,
    target.indices (L.bitRegister r) = (source.registers r).toNat
  tape_heads : ∀ t < L.tapeCount,
    target.indices (L.tapeHead t) = centered center (source.tapes t).head
  origin_word : target.indices workspaceOrigin = origin
  stride_word : target.indices bankStride = L.stride
  center_word : target.indices headCenter = center
  input_base : target.indices inputBase = origin + L.inputBank
  input_length : target.indices inputLength = bits.length
  output_base : target.indices outputBase = origin + L.outputBank
  output_length : target.indices outputLength = source.output.length
  input_cells : ∀ j < bits.length,
    target.indices (L.slot origin L.inputBank j) = (bits[j]?.getD false).toNat
  output_cells : ∀ j < source.output.length,
    target.indices (L.slot origin L.outputBank j) =
      (source.output.reverse[j]?.getD false).toNat
  stack_cells : ∀ j < source.address.length,
    target.indices (L.slot origin 1 j) =
      (source.address.reverse[j]?.getD false).toNat
  memory_cells : ∀ a, target.indices (L.slot origin 0 a) = (source.memory a).toNat
  tape_cells : ∀ t < L.tapeCount, ∀ z : ℤ, -(center : ℤ) ≤ z →
    target.indices (L.slot origin (2 + t) (centered center z)) =
      symbol ((source.tapes t).cells z)
  random_cursor : target.randomCursor = source.randomCursor

end Maxwell.Cost.RealSimulation
