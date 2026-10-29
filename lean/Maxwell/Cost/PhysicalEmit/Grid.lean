import Maxwell.Cost.PhysicalEmit.Nested
import Maxwell.Codec

set_option maxHeartbeats 800000
namespace Maxwell.Cost.PhysicalEmit
open Structured RationalAccumulator

def gridCode (body : Code) : Code := nestedCode 0 3 body

def gridWords (N : Axis → ℕ) (records : ℕ → ℕ → ℕ → List Bool) : List Bool :=
  (List.range (N 0)).flatMap fun x =>
    (List.range (N 1)).flatMap fun y => (List.range (N 2)).flatMap fun z => records x y z

theorem nestedRecords_grid (N : Axis → ℕ) (records : ℕ → ℕ → ℕ → List Bool)
    (coords : Axis → ℕ) :
    nestedRecords N (fun c => records (c 0) (c 1) (c 2)) 0 3 coords = gridWords N records := by
  simp [nestedRecords,recordPrefix,gridWords,Function.update]

theorem gridWords_cells (box : Target.Box) (records : ℕ → ℕ → ℕ → List Bool) :
    gridWords ![box.nx,box.ny,box.nz] records =
      (Codec.cells box).flatMap (fun c => records c.1.val c.2.1.val c.2.2.val) := by
  have hm (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
    ext i
    simp
  have hf (n : ℕ) (f : ℕ → List Bool) :
      (List.finRange n).flatMap (fun i => f i.val) = (List.range n).flatMap f := by
    rw [← List.flatMap_map,hm]
  have hz (x y : ℕ) : (List.finRange box.nz).flatMap (fun z => records x y z.val) =
      (List.range box.nz).flatMap (records x y) := hf _ _
  have hy (x : ℕ) : (List.finRange box.ny).flatMap (fun y =>
      (List.finRange box.nz).flatMap (fun z => records x y.val z.val)) =
      (List.range box.ny).flatMap (fun y => (List.range box.nz).flatMap (records x y)) := by
    simp only [hz]
    exact hf box.ny (fun y => (List.range box.nz).flatMap (records x y))
  have hx : (List.finRange box.nx).flatMap (fun x =>
      (List.finRange box.ny).flatMap (fun y =>
      (List.finRange box.nz).flatMap (fun z => records x.val y.val z.val))) =
      (List.range box.nx).flatMap (fun x => (List.range box.ny).flatMap
        (fun y => (List.range box.nz).flatMap (records x y))) := by
    simp only [hy]
    exact hf box.nx (fun x => (List.range box.ny).flatMap
      (fun y => (List.range box.nz).flatMap (records x y)))
  change (List.range box.nx).flatMap (fun x => (List.range box.ny).flatMap
    (fun y => (List.range box.nz).flatMap (records x y))) = _
  simpa only [Codec.cells,Codec.triples,List.flatMap_assoc,List.flatMap_map] using hx.symm

/-- The literal three-level loop emits cell records in the target codec's
order. Its control overhead is linear in the traversed box volume up to
one bit-width factor, including resetting inner loops on every row. -/
theorem grid (N : Axis → ℕ) (B Q : ℕ) (hB : ∀ a, (N a).bits.length ≤ B)
    (body : Code) (input : List Bool) (tape : ℕ → Bool)
    (R : Store → Prop) (records : ℕ → ℕ → ℕ → List Bool)
    (stable : ∀ s t, LoopFrame loopTapes s.val t.val → R s → R t)
    (bodyCorrect : ∀ x y z, x < N 0 → y < N 1 → z < N 2 → ∀ s, R s →
      LowerReady 3 N B s.val → Word s.val 240 x → Word s.val 241 y → Word s.val 242 z →
      ∃ cost t, cost ≤ Q ∧ Executes input tape body cost s t ∧ R t ∧ Held 3 s.val t.val ∧
        t.val.output = (records x y z).reverse ++ s.val.output)
    (s : Store) (hs : R s) (hr : LowerReady 0 N B s.val) :
    ∃ cost t, cost ≤ (N 0+1)*(N 1+1)*(N 2+1)*(Q+156*B+174) ∧
      Executes input tape (gridCode body) cost s t ∧ R t ∧ LowerReady 0 N B t.val ∧
      Held 0 s.val t.val ∧ t.val.output = (gridWords N records).reverse ++ s.val.output := by
  have hbody : ∀ coords : Axis → ℕ, (∀ a, coords a < N a) → ∀ s, R s →
      LowerReady 3 N B s.val → (∀ a, Word s.val (coordinateTape a) (coords a)) →
      ∃ cost t, cost ≤ Q ∧ Executes input tape body cost s t ∧ R t ∧ Held 3 s.val t.val ∧
        t.val.output = (records (coords 0) (coords 1) (coords 2)).reverse ++ s.val.output := by
    intro coords hc s hs hr hw
    exact bodyCorrect (coords 0) (coords 1) (coords 2) (hc 0) (hc 1) (hc 2) s hs hr (hw 0) (hw 1) (hw 2)
  obtain ⟨c,t,hc,he,hR,hready,hheld,ho⟩ := nested N B Q hB body input tape R
    (fun c => records (c 0) (c 1) (c 2)) stable hbody 3 0 rfl (fun _ => 0)
    (by intro a ha; omega) s hs hr (by intro a ha; omega)
  refine ⟨c,t,?_,he,hR,hready,hheld,?_⟩
  · simp [nestedBudget] at hc
    let C := 52*B+58
    have h1 : (N 2+1)*(Q+C)+C ≤ (N 2+1)*(Q+2*C) := by nlinarith
    have hp : 1 ≤ (N 1+1)*(N 2+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hsmall : C ≤ (N 1+1)*(N 2+1)*C := by simpa using Nat.mul_le_mul_right C hp
    have h2 : (N 1+1)*((N 2+1)*(Q+2*C))+C ≤ (N 1+1)*(N 2+1)*(Q+3*C) := by
      nlinarith only [hsmall]
    calc
      c ≤ (N 0+1)*((N 1+1)*((N 2+1)*(Q+C)+C)+C) := by simpa only [C,Nat.add_assoc] using hc
      _ ≤ (N 0+1)*((N 1+1)*((N 2+1)*(Q+2*C))+C) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ h1) C)
      _ ≤ (N 0+1)*((N 1+1)*(N 2+1)*(Q+3*C)) := Nat.mul_le_mul_left _ h2
      _ = _ := by dsimp [C]; ring
  · simpa only [nestedRecords_grid] using ho

end Maxwell.Cost.PhysicalEmit
