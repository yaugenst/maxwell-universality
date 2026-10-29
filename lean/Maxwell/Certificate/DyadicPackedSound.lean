import Maxwell.Certificate.DyadicPacked
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Maxwell.Certificate.DyadicKernel.Packed

theorem fits_iff (w : Nat) (a : Rectangle) : fits w a = true ↔
    0 < w ∧ -(bias w : Int) ≤ a.re ∧ a.re < (bias w : Int) ∧
      -(bias w : Int) ≤ a.im ∧ a.im < (bias w : Int) ∧ a.radius < base w := by
  simp only [fits, decide_eq_true_eq]

theorem base_pos (w : Nat) : 0 < base w := by simp [base]

theorem base_eq_twice_bias {w : Nat} (hw : 0 < w) : base w = 2*bias w := by
  unfold base bias
  have he : w = (w-1)+1 := by omega
  conv_lhs => rw [he]
  rw [pow_succ, Nat.mul_comm]

theorem slot_eq (w : Nat) : 2^(3*w) = base w ^ 3 := by
  rw [base, Nat.mul_comm 3 w, pow_mul]

private theorem offset_bounds {w : Nat} {x : Int} (hw : 0 < w)
    (hl : -(bias w : Int) ≤ x) (hu : x < (bias w : Int)) :
    0 ≤ x+(bias w : Int) ∧ (x+bias w).toNat < base w := by
  have he := base_eq_twice_bias hw
  constructor
  · omega
  · rw [Int.toNat_lt (by omega)]
    omega

theorem packRect_lt {w : Nat} {a : Rectangle} (h : fits w a = true) :
    packRect w a < 2^(3*w) := by
  obtain ⟨hw,hrl,hru,hil,hiu,hrad⟩ := (fits_iff w a).mp h
  have hr := (offset_bounds hw hrl hru).2
  have hi := (offset_bounds hw hil hiu).2
  have hb := base_pos w
  rw [slot_eq]
  unfold packRect
  have hinner : (a.im+bias w).toNat + base w*a.radius < base w^2 := by
    nlinarith
  nlinarith

theorem unpackRect_packRect {w : Nat} {a : Rectangle} (h : fits w a = true) :
    unpackRect w (packRect w a) = a := by
  obtain ⟨hw,hrl,hru,hil,hiu,hrad⟩ := (fits_iff w a).mp h
  have hr := offset_bounds hw hrl hru
  have hi := offset_bounds hw hil hiu
  have hb := base_pos w
  have hd : packRect w a / base w = (a.im+bias w).toNat+base w*a.radius := by
    rw [packRect, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hr.2, Nat.zero_add]
  have hdr : packRect w a % base w = (a.re+bias w).toNat := by
    simp [packRect, Nat.add_mod, Nat.mod_eq_of_lt hr.2]
  have hdi : (packRect w a / base w) % base w = (a.im+bias w).toNat := by
    rw [hd]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hi.2]
  have hdrr : packRect w a / base w / base w = a.radius := by
    rw [hd, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hi.2, Nat.zero_add]
  cases a
  simp only [unpackRect, hdr, hdi, hdrr, Nat.mod_eq_of_lt hrad,
    Int.toNat_of_nonneg hr.1, Int.toNat_of_nonneg hi.1, add_sub_cancel_right]


theorem unpackRect_add_slot (w n tail : Nat) :
    unpackRect w (n+2^(3*w)*tail) = unpackRect w n := by
  have hb := base_pos w
  have hs : 2^(3*w) = base w*(base w*base w) := by rw [slot_eq]; ring
  have hd : (n+2^(3*w)*tail)/base w = n/base w+(base w*base w)*tail := by
    rw [hs, Nat.mul_assoc, Nat.add_mul_div_left _ _ hb]
  have hdd : (n+2^(3*w)*tail)/base w/base w = n/base w/base w+base w*tail := by
    rw [hd, Nat.mul_assoc, Nat.add_mul_div_left _ _ hb]
  unfold unpackRect
  congr 1
  · simp [hs, Nat.add_mod, Nat.mul_mod]
  · rw [hd]
    simp [Nat.add_mod, Nat.mul_mod]
  · rw [hdd]
    simp [Nat.add_mod]

theorem unpackRect_packRects_cons {w : Nat} {a : Rectangle} (tail : List Rectangle)
    (h : fits w a = true) : unpackRect w (packRects w (a::tail)) = a := by
  rw [packRects, unpackRect_add_slot, unpackRect_packRect h]

theorem packRects_div_slot {w : Nat} {a : Rectangle} (tail : List Rectangle)
    (h : fits w a = true) : packRects w (a::tail)/2^(3*w) = packRects w tail := by
  rw [packRects, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt (packRect_lt h), Nat.zero_add]

theorem getPacked_zero (w data : Nat) : getPacked w data 0 = unpackRect w data := by
  simp [getPacked]

theorem getPacked_succ (w data idx : Nat) :
    getPacked w data (idx+1) = getPacked w (data/2^(3*w)) idx := by
  unfold getPacked
  rw [Nat.div_div_eq_div_mul, ← pow_add]
  congr 2
  congr 1
  ring

theorem getPacked_packRects {w : Nat} (a : List Rectangle)
    (h : ∀ x ∈ a, fits w x = true) (i : Nat) (hi : i < a.length) :
    getPacked w (packRects w a) i = a[i] := by
  induction a generalizing i with
  | nil => simp at hi
  | cons x tail ih =>
      have hx := h x (by simp)
      cases i with
      | zero => simpa only [getPacked_zero, List.getElem_cons_zero] using
          unpackRect_packRects_cons tail hx
      | succ i =>
          rw [getPacked_succ, packRects_div_slot tail hx]
          exact ih (fun y hy => h y (by simp [hy])) i (by simpa using hi)


theorem getPacked_packRects_ofFn {w n : Nat} (a : Fin n → Rectangle)
    (h : ∀ i, fits w (a i) = true) (i : Fin n) :
    getPacked w (packRects w (List.ofFn a)) i.val = a i := by
  have hf : ∀ x ∈ List.ofFn a, fits w x = true := by
    intro x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    exact h j
  simpa using getPacked_packRects (List.ofFn a) hf i.val (by simp)

end Maxwell.Certificate.DyadicKernel.Packed
