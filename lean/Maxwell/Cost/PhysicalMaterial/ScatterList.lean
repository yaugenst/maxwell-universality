import Maxwell.Cost.PhysicalMaterial.ScatterPoint

namespace Maxwell.Cost.PhysicalMaterial.Scatter
open Structured RationalAccumulator
set_option maxHeartbeats 1600000

def listCode : List Point → Code
  | [] => .skip
  | d::rest => .seq (pointCode d) (listCode rest)

def listBudget : List Point → ℕ → ℕ
  | [], _ => 1
  | d::rest, B => pointBudget d B + listBudget rest B

/-- A fixed prototype is compiled once into a finite sequence of local writes.
All locations below occur only in the proof of the runtime-computed addresses. -/
theorem list_executes {cells : ℕ} (l : Dense.Layout cells) (nums dens : Vector (List Bool) cells)
    (anchor : Fin 3 → ℕ) (points : List Point) (locations : Point → Fin cells)
    (ny nz B num den : ℕ) (hl : l.Sized B) (hcount : cells < 2^B)
    (hi : ∀ d ∈ points, flatIndex anchor d ny nz = (locations d).val)
    (hb : ∀ j, (anchor j).bits.length ≤ B)
    (hroom : ∀ d ∈ points, ∀ j, 0 ≤ (anchor j : ℤ)+d j)
    (hnyB : ny.bits.length ≤ B) (hnzB : nz.bits.length ≤ B)
    (hnumB : num.bits.length ≤ addressValue l.width) (hdenB : den.bits.length ≤ addressValue l.width)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hr : PointReady s.val)
    (hd : Dense.Stored l nums dens s.val)
    (ha : ∀ j, Word s.val (294+j.val) (anchor j))
    (hny : Word s.val 251 ny) (hnz : Word s.val 252 nz)
    (hnum : Word s.val 276 num) (hden : Word s.val 277 den) :
    ∃ cost t, cost ≤ listBudget points B ∧ Executes input tape (listCode points) cost s t ∧
      PointReady t.val ∧ Dense.Stored l
        (scatterWords nums (points.map locations) (FixedWidth.bits (addressValue l.width) num.bits))
        (scatterWords dens (points.map locations) (FixedWidth.bits (addressValue l.width) den.bits)) t.val ∧
      Frame s.val t.val ∧ Dense.Outside l s.val t.val := by
  induction points generalizing nums dens s with
  | nil => exact ⟨1, s, le_rfl, .skip s, hr, hd, .refl _, .refl _ _⟩
  | cons d rest ih =>
    obtain ⟨pc, a, hpc, ep, har, had, fa, oa⟩ := point l nums dens anchor d ny nz B num den hl hcount
      (locations d) (hi d (by simp)) hb (hroom d (by simp)) hnyB hnzB hnumB hdenB input tape s hr hd ha hny hnz hnum hden
    obtain ⟨rc, t, hrc, er, htr, htd, ft, ot⟩ := ih
      (nums.set (locations d) (FixedWidth.bits (addressValue l.width) num.bits))
      (dens.set (locations d) (FixedWidth.bits (addressValue l.width) den.bits))
      (fun e he => hi e (by simp [he])) (fun e he => hroom e (by simp [he])) a har had
      (fun j => word_of_eq (fa.tapes (294+j.val) (by omega) (by simp [work]; omega)) (ha j))
      (word_of_eq (fa.tapes 251 (by omega) (by decide)) hny)
      (word_of_eq (fa.tapes 252 (by omega) (by decide)) hnz)
      (word_of_eq (fa.tapes 276 (by omega) (by decide)) hnum)
      (word_of_eq (fa.tapes 277 (by omega) (by decide)) hden)
    exact ⟨pc+rc, t, Nat.add_le_add hpc hrc, ep.seq er, htr, htd, fa.trans ft, oa.trans ot⟩

def constant : List Point → ℕ
  | [] => 1
  | d::rest => coordinateFactor d+offsetWidth d+100100+constant rest

theorem pointBudget_le (d : Point) (B : ℕ) :
    pointBudget d B ≤ (coordinateFactor d+100100)*(B+offsetWidth d+3)^2 := by
  have hi := indexBudget_le d B
  have hq : (B+2)^2 ≤ (B+offsetWidth d+3)^2 := Nat.pow_le_pow_left (by omega) 2
  have hlin : B+1 ≤ (B+offsetWidth d+3)^2 := by nlinarith
  dsimp only [pointBudget]
  nlinarith

/-- The fixed-prototype scatter has polynomial binary cost independent of the
number of physical cells or runtime descriptors. -/
theorem listBudget_le (points : List Point) (B : ℕ) :
    listBudget points B ≤ constant points*(B+constant points)^2 := by
  induction points with
  | nil =>
    simp only [listBudget, constant, Nat.one_mul]
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  | cons d rest ih =>
    have hc : constant rest ≤ constant (d::rest) := by simp only [constant]; omega
    have hd : offsetWidth d+3 ≤ constant (d::rest) := by simp only [constant]; omega
    calc
      listBudget (d::rest) B = pointBudget d B+listBudget rest B := rfl
      _ ≤ (coordinateFactor d+100100)*(B+constant (d::rest))^2 +
          constant rest*(B+constant (d::rest))^2 := by
        apply Nat.add_le_add
        · exact (pointBudget_le d B).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
        · exact ih.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
      _ ≤ constant (d::rest)*(B+constant (d::rest))^2 := by
        rw [← Nat.add_mul]
        apply Nat.mul_le_mul_right
        simp only [constant]
        omega

end Maxwell.Cost.PhysicalMaterial.Scatter
