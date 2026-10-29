import Maxwell.Cost.SplitNode.Common

namespace Maxwell.Cost.RoutingAllocator

/-- A node reserves eleven equally sized bit-array slabs. -/
def slab (frontier n width i : ℕ) : ℕ := frontier+i*(n*width)

def nextFrontier (frontier n width : ℕ) : ℕ := slab frontier n width 11

def parentOutput (frontier n width : ℕ) : ℕ := slab frontier n width 10

def layout (frontier n width forward backward : ℕ) : SplitNode.Layout where
  split := ⟨⟨width,slab frontier n width 2,slab frontier n width 3,
    slab frontier n width 4,slab frontier n width 5⟩,
    forward,backward,slab frontier n width 0,slab frontier n width 1⟩
  childBases i := slab frontier n width (6+i.val)

theorem slab_lower (frontier n width i : ℕ) : frontier ≤ slab frontier n width i := by
  unfold slab; omega

theorem slab_upper (frontier n width i : ℕ) (hi : i<11) :
    slab frontier n width i+n*width ≤ nextFrontier frontier n width := by
  have hh := Nat.mul_le_mul_right (n*width) (show i+1 ≤ 11 by omega)
  dsimp only [nextFrontier,slab]
  nlinarith only [hh]

theorem slab_separated (frontier n width i j : ℕ) (hij : i ≠ j) :
    IncidenceEncoding.Separated (slab frontier n width i) (n*width)
      (slab frontier n width j) (n*width) := by
  rcases lt_or_gt_of_ne hij with hij|hij
  · left
    have hh := Nat.mul_le_mul_right (n*width) (show i+1 ≤ j by omega)
    unfold slab
    nlinarith only [hh]
  · right
    have hh := Nat.mul_le_mul_right (n*width) (show j+1 ≤ i by omega)
    unfold slab
    nlinarith only [hh]

private theorem separated_shrink {a b x y x' y' : ℕ}
    (h : IncidenceEncoding.Separated a x b y) (hx : x' ≤ x) (hy : y' ≤ y) :
    IncidenceEncoding.Separated a x' b y' := by
  rcases h with h|h
  · left; omega
  · right; omega

theorem split_separated (frontier n width forward backward : ℕ)
    (hforward : forward+n*width ≤ frontier) (hbackward : backward+n*width ≤ frontier)
    (hsource : IncidenceEncoding.Separated forward (n*width) backward (n*width)) :
    (layout frontier n width forward backward).split.Separated n := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals simp only [layout,BinarySplit.Layout.base,Fin.reduceFinMk,slab] at *
  all_goals first
  | exact hsource
  | exact hsource.symm
  | (unfold IncidenceEncoding.Separated at *; omega)

private theorem after_eq (route : DoublingPass.Layout) (rounds : ℕ) :
    DoublingPass.layoutAfter route rounds=route ∨ DoublingPass.layoutAfter route rounds=route.flip := by
  induction rounds with
  | zero => exact Or.inl rfl
  | succ rounds ih =>
    rcases ih with h|h
    · exact Or.inr (by simp [DoublingPass.layoutAfter,h])
    · exact Or.inl (by simp [DoublingPass.layoutAfter,h])

theorem child_separated (frontier forward backward k : ℕ)
    (hforward : forward+(2*2^k)*(k+2) ≤ frontier) :
    ((layout frontier (2*2^k) (k+2) forward backward).child (2*2^k)).Separated k := by
  let n := 2*2^k
  let w := k+2
  have hlen : 2^k*(w-1) ≤ n*w := by dsimp [n,w]; nlinarith [Nat.zero_le (2^k)]
  have hcolors : n ≤ n*w := by dsimp [w]; nlinarith
  constructor
  · intro i j hij
    have hv : 6+i.val ≠ 6+j.val := by intro h; apply hij; apply Fin.ext; omega
    rw [SplitNode.Layout.child_outputBase,SplitNode.Layout.child_outputBase]
    change IncidenceEncoding.Separated (slab frontier n w (6+i.val)) (2^k*(w-1))
      (slab frontier n w (6+j.val)) (2^k*(w-1))
    exact separated_shrink (slab_separated frontier n w (6+i.val) (6+j.val) hv) hlen hlen
  · intro i
    left
    rw [SplitNode.Layout.child_outputBase]
    change forward+n*w ≤ slab frontier n w (6+i.val)
    exact hforward.trans (slab_lower _ _ _ _)
  · intro i
    have hs := after_eq (layout frontier n w forward backward).split.route n.bits.length
    rcases hs with hs|hs
    all_goals left
    all_goals rw [SplitNode.Layout.child_outputBase]
    all_goals change (DoublingPass.layoutAfter (layout frontier n w forward backward).split.route n.bits.length).newJump+n ≤ slab frontier n w (6+i.val)
    all_goals rw [hs]
    all_goals simp only [layout,DoublingPass.Layout.flip,slab]
    all_goals have h := Nat.mul_le_mul_right (n*w) (show (4:ℕ)+1 ≤ 6+i.val by omega)
    all_goals nlinarith only [h,hcolors]

end Maxwell.Cost.RoutingAllocator
