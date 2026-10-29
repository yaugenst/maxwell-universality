import Maxwell.Cost.HalfPair
import Maxwell.Cost.ConjugatePass
import Maxwell.Cost.CycleSplit
import Maxwell.Cost.Structured.WordAssign

namespace Maxwell.Cost.BinarySplit

structure Layout where
  route : DoublingPass.Layout
  forward : ℕ
  backward : ℕ
  pairing : ℕ
  conjugated : ℕ

def Layout.base (layout : Layout) (i : Fin 8) : ℕ :=
  match i.val with
  | 0 => layout.forward
  | 1 => layout.backward
  | 2 => layout.pairing
  | 3 => layout.conjugated
  | 4 => layout.route.oldJump
  | 5 => layout.route.oldMinimum
  | 6 => layout.route.newJump
  | _ => layout.route.newMinimum

def Layout.Separated (layout : Layout) (n : ℕ) : Prop :=
  ∀ i j : Fin 8, i≠j → IncidenceEncoding.Separated (layout.base i) (n*layout.route.width)
    (layout.base j) (n*layout.route.width)

def Layout.half (layout : Layout) : DoublingInit.Layout :=
  ⟨{layout.route with newMinimum := layout.pairing},layout.pairing,layout.conjugated⟩

def Layout.conjugate (layout : Layout) : DoublingPass.Layout :=
  ⟨layout.route.width,layout.forward,layout.pairing,layout.backward,layout.conjugated⟩

def Layout.cycle (layout : Layout) : DoublingInit.Layout :=
  ⟨layout.route,layout.pairing,layout.conjugated⟩

theorem Layout.Separated.conjugate {layout : Layout} {n : ℕ} (h : layout.Separated n) :
    ConjugatePass.Separated layout.conjugate n :=
  ⟨h 0 3 (by decide),h 2 3 (by decide),h 1 3 (by decide)⟩

theorem Layout.Separated.cycle {layout : Layout} {n : ℕ} (h : layout.Separated n) :
    layout.cycle.Separated n := by
  intro i j hij
  let lift (i : Fin 6) : Fin 8 := ⟨i.val+2,by omega⟩
  have neq : lift i≠lift j := by intro he; apply hij; apply Fin.ext; have hv := congrArg Fin.val he; dsimp [lift] at hv; omega
  have base (i : Fin 6) : layout.cycle.base i=layout.base (lift i) := by
    fin_cases i <;> rfl
  change IncidenceEncoding.Separated (layout.cycle.base i) (n*layout.route.width) (layout.cycle.base j) (n*layout.route.width)
  rw [base,base]
  exact h (lift i) (lift j) neq

/-- A one-output-interval execution preserves every disjoint array. -/
theorem represents_outside {n : ℕ} {before after : ℕ → Bool}
    {base width outputBase outputLength : ℕ} {words : Vector (List Bool) n}
    (frame : ∀ p, p<outputBase ∨ outputBase+outputLength≤p → after p=before p)
    (apart : IncidenceEncoding.Separated base (n*width) outputBase outputLength)
    (rep : BitArray.Represents before base width words) :
    BitArray.Represents after base width words where
  length := rep.length
  bits i j hj := by
    rw [frame (base+i.val*width+j) (by
      rcases apart with hl | hr
      · left
        have hmul : i.val*width+width≤n*width := by nlinarith [Nat.mul_le_mul_right width (Nat.succ_le_of_lt i.isLt)]
        omega
      · right; omega)]
    exact rep.bits i j hj

theorem Layout.Separated.apart_route {layout : Layout} {n : ℕ} (h : layout.Separated n)
    (i : Fin 4) : CycleSplit.Apart layout.route (layout.base ⟨i.val,by omega⟩) n :=
  ⟨h ⟨i.val,by omega⟩ 4 (by intro he; have hv : i.val=4 := congrArg Fin.val he; omega),
   h ⟨i.val,by omega⟩ 5 (by intro he; have hv : i.val=5 := congrArg Fin.val he; omega),
   h ⟨i.val,by omega⟩ 6 (by intro he; have hv : i.val=6 := congrArg Fin.val he; omega),
   h ⟨i.val,by omega⟩ 7 (by intro he; have hv : i.val=7 := congrArg Fin.val he; omega)⟩

end Maxwell.Cost.BinarySplit
