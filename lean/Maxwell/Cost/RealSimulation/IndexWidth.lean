import Maxwell.Cost.Execution
import Mathlib.Data.Nat.Size

namespace Maxwell.Cost.RealSimulation.IndexWidth

/-- Every natural word is bounded, including words used as indirect addresses. -/
def IndexBound (B : ℕ) (s : RAMState) : Prop := ∀ j, s.indices j ≤ B

def LiteralBound (K : ℕ) (M : Machine) : Prop :=
  ∀ dst value, RAMInstruction.indexLiteral dst value ∈ M.code → value ≤ K

def InputBound (K : ℕ) (input : RAMInput) : Prop := ∀ j, input.indices j ≤ K

theorem IndexBound.mono {B C : ℕ} {s : RAMState}
    (h : IndexBound B s) (hBC : B ≤ C) : IndexBound C s :=
  fun j => (h j).trans hBC

theorem IndexBound.setIndex {B : ℕ} {s : RAMState} (h : IndexBound B s)
    (dst value : ℕ) (hv : value ≤ B) : IndexBound B (s.setIndex dst value) := by
  intro j
  simp only [RAMState.setIndex, Function.update_apply]
  split_ifs
  · exact hv
  · exact h j

/-- Addition is the only instruction that can enlarge an existing index word.
Indirect loads/stores select from the same globally bounded index bank. -/
theorem next_bound {M : Machine} {input : RAMInput} {tape : ℕ → Bool}
    {B K : ℕ} {s t : RAMState} (hs : IndexBound B s)
    (hc : LiteralBound K M) (hi : InputBound K input)
    (h : M.next input tape s = some t) :
    IndexBound (2 * max B K) t := by
  have hB : B ≤ 2 * max B K := by have := le_max_left B K; omega
  have hK : K ≤ 2 * max B K := by have := le_max_right B K; omega
  cases hop : M.code[s.pc]? with
  | none => simp [Machine.next, hop] at h
  | some op =>
    cases op <;> simp only [Machine.next, hop, Option.some.injEq, reduceCtorEq] at h
    all_goals subst t
    all_goals try exact hs.mono hB
    all_goals apply (hs.mono hB).setIndex
    all_goals try exact (hi _).trans hK
    all_goals try exact (hs _).trans hB
    all_goals try exact (hc _ _ (List.mem_of_getElem? hop)).trans hK
    case indexAdd dst left right =>
      have hl := hs left
      have hr := hs right
      have := le_max_left B K
      omega
    case indexSubtract dst left right => exact (Nat.sub_le _ _).trans ((hs left).trans hB)

theorem next_bound_succ {M : Machine} {input : RAMInput} {tape : ℕ → Bool}
    {B K : ℕ} {s t : RAMState} (hs : IndexBound B s)
    (hc : LiteralBound K M) (hi : InputBound K input)
    (h : M.next input tape s = some t) :
    IndexBound (2 * (max B K + 1)) t :=
  (next_bound hs hc hi h).mono (by omega)

/-- A fixed literal/input cap already below the initial bound remains absorbed
in the doubling bound at every actual transition. -/
theorem steps_bound_of_le {M : Machine} {input : RAMInput} {tape : ℕ → Bool}
    {B K k : ℕ} {s t : RAMState} (hs : IndexBound B s)
    (hc : LiteralBound K M) (hi : InputBound K input) (hKB : K ≤ B)
    (h : Steps (M.next input tape) k s t) : IndexBound (2 ^ k * B) t := by
  induction h generalizing B with
  | refl s => simpa using hs
  | @step n s t u h rest ih =>
    have ht : IndexBound (2 * B) t := by
      simpa [max_eq_left hKB] using next_bound hs hc hi h
    have hu := ih ht (show K ≤ 2 * B by omega)
    simpa [pow_succ, Nat.mul_assoc] using hu

theorem steps_bound {M : Machine} {input : RAMInput} {tape : ℕ → Bool}
    {B K k : ℕ} {s t : RAMState} (hs : IndexBound B s)
    (hc : LiteralBound K M) (hi : InputBound K input)
    (h : Steps (M.next input tape) k s t) :
    IndexBound (2 ^ k * (B + K + 1)) t :=
  steps_bound_of_le (hs.mono (by omega)) hc hi (by omega) h

theorem steps_width {M : Machine} {input : RAMInput} {tape : ℕ → Bool}
    {B K k : ℕ} {s t : RAMState} (hs : IndexBound B s)
    (hc : LiteralBound K M) (hi : InputBound K input)
    (h : Steps (M.next input tape) k s t) (j : ℕ) :
    (t.indices j).size ≤ k + (B + K + 1).size := by
  apply Nat.size_le.mpr
  have hb := steps_bound hs hc hi h j
  have hp : 0 < 2 ^ k := Nat.pow_pos (by decide)
  have hh := Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self (B + K + 1)) hp
  rw [← pow_add] at hh
  exact hb.trans_lt hh

/-- This is a segment bound with explicit entry and code/input bounds. It does
not assume that an earlier or later segment satisfies the same entry cap. -/
theorem segment_width {M : Machine} {input : RAMInput} {tape : ℕ → Bool}
    {B K k C W : ℕ} {s t : RAMState} (hs : IndexBound B s)
    (hc : LiteralBound K M) (hi : InputBound K input)
    (hB : B ≤ 2 ^ W) (hK : K ≤ 2 ^ W)
    (hcost : k ≤ C * (W + 1)) (h : Steps (M.next input tape) k s t) (j : ℕ) :
    (t.indices j).size ≤ (C + 1) * (W + 1) := by
  have hb := steps_bound_of_le (hs.mono hB) hc hi hK h j
  rw [← pow_add] at hb
  have hw := Nat.size_le_size hb
  rw [Nat.size_pow] at hw
  calc
    (t.indices j).size ≤ k + W + 1 := hw
    _ ≤ C * (W + 1) + (W + 1) := by omega
    _ = (C + 1) * (W + 1) := by rw [Nat.add_mul, Nat.one_mul]

end Maxwell.Cost.RealSimulation.IndexWidth
