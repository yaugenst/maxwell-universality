import Maxwell.Green.CalibrationIndex
import Maxwell.Green.CalibrationSupport
import Maxwell.Cost.Structured.NatAssign.Bounds

/-! Actual mixed-radix addresses of the fixed defect's translated source
edges. Every variable operation is natural addition or multiplication. -/
namespace Maxwell.Cost.CalibrationSource
open Defect.FiniteStencil Spectral Spectral.Lattice
open Green.PhysicalCompression
open Structured
set_option maxHeartbeats 1000000

/-- The source work cube includes the complete propagation stencil. -/
def radius (R0 L d N : ℕ) : ℕ := R0+20*L*d+4*N+2

/-- A nonnegative constant coefficient for each translated coordinate. -/
def slope (L : ℕ) (v : Site) (j : Direction) : ℕ := ((L : ℤ)-v j).toNat

def digit (R0 L : ℕ) (v : Site) (e : Edge) (d N : ℕ) (j : Direction) : ℕ :=
  ((R0 : ℤ)+e.2 j).toNat+4*N+2+20*slope L v j*d

def address (R0 L : ℕ) (v : Site) (e : Edge) (d N : ℕ) : ℕ :=
  let w := cubeWidth (radius R0 L d N)
  digit R0 L v e d N 2+w*(digit R0 L v e d N 1+
    w*(digit R0 L v e d N 0+w*e.1.val))

theorem digit_cast (R0 L : ℕ) (v : Site) (e : Edge) (d N : ℕ)
    (he : ∀ j, |e.2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |v j| ≤ (L : ℤ)) (j : Direction) :
    (digit R0 L v e d N j : ℤ) = (radius R0 L d N : ℤ)+e.2 j-20*(d : ℤ)*v j := by
  have he0 : 0 ≤ (R0 : ℤ)+e.2 j := by have := (abs_le.mp (he j)).1; omega
  have hv0 : 0 ≤ (L : ℤ)-v j := by have := (abs_le.mp (hv j)).2; omega
  simp only [digit,slope,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Int.toNat_of_nonneg he0,
    Int.toNat_of_nonneg hv0,radius]
  ring

theorem translated_bound (R0 L : ℕ) (v : Site) (e : Edge) (d N : ℕ)
    (he : ∀ j, |e.2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |v j| ≤ (L : ℤ)) (j : Direction) :
    |(translateEdge ((d : ℤ) • v) e).2 j| ≤ (radius R0 L d N : ℤ) := by
  change |e.2 j-20*((d : ℤ)*v j)| ≤ _
  have hd : (0 : ℤ) ≤ d := by positivity
  have hv' := mul_le_mul_of_nonneg_left (hv j) (show (0 : ℤ) ≤ 20*d by positivity)
  calc
    _ ≤ |e.2 j|+|20*((d : ℤ)*v j)| := abs_sub _ _
    _ = |e.2 j|+20*(d : ℤ)*|v j| := by rw [abs_mul,abs_mul,abs_of_nonneg hd]; norm_num; ring
    _ ≤ (R0 : ℤ)+20*d*L := add_le_add (he j) hv'
    _ ≤ _ := by dsimp [radius]; nlinarith

theorem address_eq_radixIndex (R0 L : ℕ) (v : Site) (e : Edge) (d N : ℕ)
    (he : ∀ j, |e.2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |v j| ≤ (L : ℤ)) :
    address R0 L v e d N =
      (radixIndex (radius R0 L d N) (translateEdge ((d : ℤ) • v) e)
        (translated_bound R0 L v e d N he hv)).val := by
  rw [radixIndex_val]
  have hd (j : Direction) :
      ((translateEdge ((d : ℤ) • v) e).2 j+(radius R0 L d N : ℤ)).toNat = digit R0 L v e d N j := by
    rw [← Int.toNat_natCast (digit R0 L v e d N j),digit_cast R0 L v e d N he hv j]
    congr 1
    change e.2 j-20*((d : ℤ)*v j)+_ = _
    ring
  rw [hd 2,hd 1,hd 0]
  simp only [translateEdge,address]
  ring

theorem address_lt (R0 L : ℕ) (v : Site) (e : Edge) (d N : ℕ)
    (he : ∀ j, |e.2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |v j| ≤ (L : ℤ)) :
    address R0 L v e d N < 3*cubeWidth (radius R0 L d N)^3 := by
  rw [address_eq_radixIndex R0 L v e d N he hv]
  exact (radixIndex _ _ _).isLt

theorem address_edge (R0 L : ℕ) (v : Site) (e : Edge) (d N : ℕ)
    (he : ∀ j, |e.2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |v j| ≤ (L : ℤ)) :
    radixCubeEmbedding (radius R0 L d N)
      ⟨address R0 L v e d N,address_lt R0 L v e d N he hv⟩ = translateEdge ((d : ℤ) • v) e := by
  have hi : (⟨address R0 L v e d N,address_lt R0 L v e d N he hv⟩ :
      Fin (3*cubeWidth (radius R0 L d N)^3)) =
      radixIndex (radius R0 L d N) (translateEdge ((d : ℤ) • v) e)
        (translated_bound R0 L v e d N he hv) :=
    Fin.ext (address_eq_radixIndex R0 L v e d N he hv)
  rw [hi]
  exact radixEdge_radixIndex _ _ _

end Maxwell.Cost.CalibrationSource
