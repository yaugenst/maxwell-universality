import Maxwell.Composition.SourceSeedWords
import Maxwell.Codec.EdgeIndex

/-! Exact prefixValues semantics for the source writer. Each original source row
visits the fixed prototype once; injective physical placement makes every
scatter a single overwrite, with no summation or denominator accumulation. -/
noncomputable section
namespace Maxwell.Composition.SourceSeedScatter
open Maxwell.Composition.PhysicalGram Maxwell.Composition.PhysicalSource
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1500000

variable (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
variable (ζ : ℚ) (hζ : 0<ζ) (hζ1 : ζ≤1) (hd : P.spacing.minimumDistance≤d)

abbrev Count := S.n*(Maxwell.Defect.ScalarDefect.edges P.defect).card

def key (i : Fin (Count P S)) : (box P S precision d ζ hζ hζ1).Edge :=
  SourceSeedStream.edge P S precision d ζ hζ hζ1 hd (finProdFinEquiv.symm i)

def value (q : Local P→ℚ) (i : Fin (Count P S)) : ℚ :=
  SourceSeedStream.value P S q (finProdFinEquiv.symm i)

theorem key_injective : Function.Injective (key P S precision d ζ hζ hζ1 hd) :=
  (SourceSeedStream.edge_injective P S precision d ζ hζ hζ1 hd).comp finProdFinEquiv.symm.injective

def prefixValues (q : Local P→ℚ) : ℕ → ((box P S precision d ζ hζ hζ1).Edge→ℚ)
  | 0 => fun _ => 0
  | t+1 => if h : t<Count P S then
      Function.update (prefixValues q t) (key P S precision d ζ hζ hζ1 hd ⟨t,h⟩) (value P S q ⟨t,h⟩)
    else prefixValues q t

theorem prefix_at (q : Local P→ℚ) (t : ℕ) (i : Fin (Count P S)) :
    prefixValues P S precision d ζ hζ hζ1 hd q t (key P S precision d ζ hζ hζ1 hd i) =
      if i.val<t then value P S q i else 0 := by
  induction t with
  | zero => simp [prefixValues]
  | succ t ih =>
    rw [prefixValues]
    by_cases ht : t<Count P S
    · rw [dite_eq_left ht]
      by_cases hi : i.val=t
      · have he : i=⟨t,ht⟩ := Fin.ext hi
        subst i
        rw [Function.update_self]
        simp
      · have hk : key P S precision d ζ hζ hζ1 hd i ≠
          key P S precision d ζ hζ hζ1 hd ⟨t,ht⟩ := by
          intro hh
          exact hi (congrArg Fin.val ((key_injective P S precision d ζ hζ hζ1 hd) hh))
        rw [Function.update_of_ne hk,ih]
        have hiff : i.val<t+1 ↔ i.val<t := by omega
        simp only [hiff]
    · rw [dite_eq_right ht,ih]
      have hi := i.isLt
      have h1 : i.val<t := by omega
      simp [h1,show i.val<t+1 by omega]

theorem prefix_off (q : Local P→ℚ) (t : ℕ)
    (e : (box P S precision d ζ hζ hζ1).Edge)
    (he : ∀ i, key P S precision d ζ hζ hζ1 hd i ≠ e) :
    prefixValues P S precision d ζ hζ hζ1 hd q t e=0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [prefixValues]
    split_ifs with ht
    · rw [Function.update_of_ne (Ne.symm (he ⟨t,ht⟩)),ih]
    · exact ih

/-- All and only the actual seed entries result from the n-by-prototype
write sequence; this identity is independent of the random draw. -/
theorem full_eq_seed (q : Local P→ℚ) :
    prefixValues P S precision d ζ hζ hζ1 hd q (Count P S) =
      seed P S precision d ζ hζ hζ1 hd q (SourceRational.decorated S precision) := by
  classical
  funext e
  by_cases he : ∃ i, key P S precision d ζ hζ hζ1 hd i=e
  · obtain ⟨i,rfl⟩ := he
    rw [prefix_at,ite_eq_left i.isLt]
    exact (SourceSeedStream.seed_at P S precision d ζ hζ hζ1 hd q (finProdFinEquiv.symm i)).symm
  · have hn : ∀ i, key P S precision d ζ hζ hζ1 hd i≠e := by simpa using he
    rw [prefix_off P S precision d ζ hζ hζ1 hd q _ e hn]
    symm
    apply SourceSeedStream.seed_off
    intro ik hk
    apply hn (finProdFinEquiv ik)
    simpa only [key,Equiv.symm_apply_apply] using hk

end Maxwell.Composition.SourceSeedScatter
