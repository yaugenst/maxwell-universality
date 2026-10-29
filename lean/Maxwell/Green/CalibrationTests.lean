import Maxwell.Green.CalibrationTable

/-! Twelve unsigned equality tests suffice for every local stencil key. -/
namespace Maxwell.Defect.FiniteStencil
open Spectral Spectral.Lattice
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def freeTemplate (d : Direction) (k : Fin 16) : Edge × ℚ :=
  (freeStencilTerms (d, 0))[k.val]'(by rw [freeStencilTerms_length]; exact k.isLt)

/-- Every stencil coordinate offset is one of minus one, zero and one. -/
theorem freeTemplate_coordinate_bound : ∀ (d : Direction) (k : Fin 16) (j : Direction),
    -1 ≤ (freeTemplate d k).1.2 j ∧ (freeTemplate d k).1.2 j ≤ 1 := by decide

def offsetIndex (d : Direction) (k : Fin 16) (j : Direction) : Fin 3 :=
  ⟨((freeTemplate d k).1.2 j + 1).toNat, by
    have h := freeTemplate_coordinate_bound d k j
    omega⟩

/-- Natural-coordinate comparison banks need only the unshifted coordinate
and its successor; the common signed cube origin cancels. -/
def coordinateTest (x y : ℕ) (delta : Fin 3) : Bool :=
  decide (x + (if delta = 0 then 1 else 0) = y + (if delta = 2 then 1 else 0))

def directionTests (rowDirection : Direction) : Direction → Bool :=
  fun d => decide (rowDirection = d)

def coordinateTests (row column : Direction → ℕ) : Direction → Fin 3 → Bool :=
  fun j delta => coordinateTest (row j) (column j) delta

def fixedHit (d : Direction) (k : Fin 16) (direction : Direction → Bool)
    (coordinates : Direction → Fin 3 → Bool) : Bool :=
  direction (freeTemplate d k).1.1 &&
    (coordinates 0 (offsetIndex d k 0) &&
    (coordinates 1 (offsetIndex d k 1) && coordinates 2 (offsetIndex d k 2)))

def unsignedEdge (R : ℕ) (d : Direction) (digits : Direction → ℕ) : Edge :=
  (d, fun j => (digits j : ℤ) - R)

private theorem coordinateTest_spec (x y : ℕ) (a : ℤ) (ha : -1 ≤ a ∧ a ≤ 1) :
    coordinateTest x y ⟨(a + 1).toNat, by omega⟩ = true ↔ (x : ℤ) = y + a := by
  rcases ha with ⟨ha, hb⟩
  interval_cases a <;> norm_num [coordinateTest] <;> omega

/-- The sixteen material-independent key bits are fixed Boolean
conjunctions of three direction comparisons and nine coordinate comparisons. -/
theorem fixedHit_binding (R : ℕ) (rowDirection columnDirection : Direction)
    (row column : Direction → ℕ) (k : Fin 16) :
    fixedHit columnDirection k (directionTests rowDirection) (coordinateTests row column) =
      (entryKey (unsignedEdge R rowDirection row) (unsignedEdge R columnDirection column)).hit k := by
  apply Bool.eq_iff_iff.mpr
  simp only [fixedHit, Bool.and_eq_true, directionTests, decide_eq_true_eq,
    coordinateTests, offsetIndex, coordinateTest_spec _ _ _ (freeTemplate_coordinate_bound _ _ _),
    entryKey, unsignedEdge, translateEdge, Prod.mk.injEq]
  constructor
  · rintro ⟨hd, h0, h1, h2⟩
    dsimp only [freeTemplate] at h0 h1 h2
    refine ⟨hd, funext fun j => ?_⟩
    fin_cases j
    · change (row 0 : ℤ) - R = (freeStencilTerms (columnDirection, 0))[k.val].1.2 0 + ((column 0 : ℤ) - R)
      omega
    · change (row 1 : ℤ) - R = (freeStencilTerms (columnDirection, 0))[k.val].1.2 1 + ((column 1 : ℤ) - R)
      omega
    · change (row 2 : ℤ) - R = (freeStencilTerms (columnDirection, 0))[k.val].1.2 2 + ((column 2 : ℤ) - R)
      omega
  · rintro ⟨hd, hcoords⟩
    refine ⟨hd, ?_, ?_, ?_⟩
    · have h := congrFun hcoords 0
      dsimp only [Pi.add_apply, freeTemplate] at h ⊢
      omega
    · have h := congrFun hcoords 1
      dsimp only [Pi.add_apply, freeTemplate] at h ⊢
      omega
    · have h := congrFun hcoords 2
      dsimp only [Pi.add_apply, freeTemplate] at h ⊢
      omega

def fixedDiagonal (d : Direction) (direction : Direction → Bool)
    (coordinates : Direction → Fin 3 → Bool) : Bool :=
  direction d && (coordinates 0 1 && (coordinates 1 1 && coordinates 2 1))

/-- The same saved equality results also supply the material diagonal bit. -/
theorem fixedDiagonal_binding (R : ℕ) (rd cd : Direction) (row column : Direction → ℕ) :
    fixedDiagonal cd (directionTests rd) (coordinateTests row column) =
      (entryKey (unsignedEdge R rd row) (unsignedEdge R cd column)).diagonal := by
  apply Bool.eq_iff_iff.mpr
  simp only [fixedDiagonal, Bool.and_eq_true, directionTests, coordinateTests,
    coordinateTest, entryKey, unsignedEdge, decide_eq_true_eq, Prod.mk.injEq]
  change (rd = cd ∧ row 0 = column 0 ∧ row 1 = column 1 ∧ row 2 = column 2) ↔ _
  constructor
  · rintro ⟨hd, h0, h1, h2⟩
    refine ⟨hd, funext fun j => ?_⟩
    fin_cases j
    · change (row 0 : ℤ) - R = (column 0 : ℤ) - R
      rw [h0]
    · change (row 1 : ℤ) - R = (column 1 : ℤ) - R
      rw [h1]
    · change (row 2 : ℤ) - R = (column 2 : ℤ) - R
      rw [h2]
  · rintro ⟨hd, he⟩
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    have h2 := congrFun he 2
    refine ⟨hd, ?_, ?_, ?_⟩ <;> omega

end Maxwell.Defect.FiniteStencil
