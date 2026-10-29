import Maxwell.Cost.DecoderParser.Schema

namespace Maxwell.Cost.DecoderParser

/-- A bound on every natural binary field, including list counts. -/
def WidthBound : (shape : Shape) → Payload shape → ℕ → Prop
  | .bit, _, _ => True
  | .nat, n, B => n.bits.length ≤ B
  | .pair left right, (x,y), B => WidthBound left x B ∧ WidthBound right y B
  | .list element, xs, B => xs.length.bits.length ≤ B ∧ ∀ x ∈ xs, WidthBound element x B

def shapeConstant : Shape → ℕ
  | .bit => 5
  | .nat => 71
  | .pair left right => max (shapeConstant left) (shapeConstant right)
  | .list element => shapeConstant element + 100

theorem wire_nonempty (shape : Shape) (x : Payload shape) : 1 ≤ (wire shape x).length := by
  induction shape with
  | bit => simp [wire]
  | nat => simp [wire,Codec.nat];omega
  | pair left right ihl ihr => rcases x with ⟨x,y⟩; simp only [wire,List.length_append]; have := ihl x; omega
  | list element ih => simp [wire,Codec.list,Codec.nat];omega

theorem records_length_lower (shape : Shape) (xs : List (Payload shape)) :
    xs.length ≤ (xs.flatMap (wire shape)).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := wire_nonempty shape x
    simp only [List.length_cons,List.flatMap_cons,List.length_append]
    omega

/-- An actual computable maximum over the fields present in the wire. -/
def maxWidth : (shape : Shape) → Payload shape → ℕ
  | .bit, _ => 0
  | .nat, n => n.bits.length
  | .pair left right, (x,y) => max (maxWidth left x) (maxWidth right y)
  | .list element, xs => max xs.length.bits.length ((xs.map (maxWidth element)).foldr max 0)

theorem WidthBound.mono (shape : Shape) (x : Payload shape) {a b : ℕ}
    (h : WidthBound shape x a) (hab : a ≤ b) : WidthBound shape x b := by
  induction shape with
  | bit => trivial
  | nat => exact h.trans hab
  | pair left right ihl ihr => rcases x with ⟨x,y⟩; exact ⟨ihl x h.1, ihr y h.2⟩
  | list element ih => exact ⟨h.1.trans hab,fun v hv => ih v (h.2 v hv)⟩

private theorem member_fold_max {α : Type*} (f : α → ℕ) (xs : List α) (x : α) (hx : x ∈ xs) :
    f x ≤ (xs.map f).foldr max 0 := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp
    · exact (ih hx).trans (le_max_right _ _)

theorem maxWidth_correct (shape : Shape) (x : Payload shape) : WidthBound shape x (maxWidth shape x) := by
  induction shape with
  | bit => trivial
  | nat => exact le_rfl
  | pair left right ihl ihr =>
    rcases x with ⟨x,y⟩
    exact ⟨(ihl x).mono _ _ (le_max_left _ _),(ihr y).mono _ _ (le_max_right _ _)⟩
  | list element ih =>
    refine ⟨le_max_left _ _,?_⟩
    intro v hv
    exact (ih v).mono _ _ ((member_fold_max (maxWidth element) x v hv).trans (le_max_right _ _))

/-- Parsing is linear in the actual encoded bits, multiplied only by the
largest binary field width. Nested list lengths do not become free counters. -/
theorem price_le (shape : Shape) (x : Payload shape) (B : ℕ) (h : WidthBound shape x B) :
    price shape x ≤ shapeConstant shape * (wire shape x).length * (B+1) := by
  induction shape with
  | bit => simp [price,wire,shapeConstant]
  | nat =>
    dsimp [price,wire,shapeConstant]
    simp only [Codec.nat,List.length_append,List.length_replicate,List.length_cons]
    dsimp [WidthBound] at h
    nlinarith
  | pair left right ihl ihr =>
    rcases x with ⟨x,y⟩
    obtain ⟨hl,hr⟩ := h
    have h1 := ihl x hl
    have h2 := ihr y hr
    have h1' : price left x ≤ max (shapeConstant left) (shapeConstant right) *
        (wire left x).length * (B+1) :=
      h1.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (le_max_left _ _)))
    have h2' : price right y ≤ max (shapeConstant left) (shapeConstant right) *
        (wire right y).length * (B+1) :=
      h2.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (le_max_right _ _)))
    simp only [price,wire,shapeConstant,List.length_append]
    nlinarith
  | list element ih =>
    obtain ⟨hcount,helements⟩ := h
    have hsumAux (xs : List (Payload element))
        (hall : ∀ v ∈ xs, WidthBound element v B) :
        (xs.map (price element)).sum ≤
          shapeConstant element * (xs.flatMap (wire element)).length * (B+1) := by
      induction xs with
      | nil => simp
      | cons v vs ihlist =>
        have hv := ih v (hall v (by simp))
        have ht := ihlist (by intro a ha; exact hall a (by simp [ha]))
        simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append]
        nlinarith
    have hsum := hsumAux x helements
    have hlen := records_length_lower element x
    have hheader : 71*x.length.bits.length+67 ≤ 71*(B+1) := by omega
    have hcounter : (x.length+1)*(13*x.length.bits.length+15) ≤
        (x.length+1)*(15*(B+1)) := Nat.mul_le_mul_left _ (by omega)
    have hcount_len : x.length+1 ≤ (wire (.list element) x).length := by
      simp only [wire,Codec.list,Codec.nat,List.length_append,List.length_replicate,List.length_cons]
      omega
    have hpositive := wire_nonempty (.list element) x
    have hrecords : (x.flatMap (wire element)).length ≤ (wire (.list element) x).length := by
      simp only [wire,Codec.list,List.length_append];omega
    have hs : (x.map (price element)).sum ≤
        shapeConstant element * (wire (.list element) x).length * (B+1) :=
      hsum.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hrecords))
    have hc := hcounter.trans (Nat.mul_le_mul_right (15*(B+1)) hcount_len)
    have hh : 71*x.length.bits.length+67 ≤ 71*(wire (.list element) x).length*(B+1) :=
      hheader.trans (Nat.mul_le_mul_right _ (by omega))
    change 71*x.length.bits.length+67 +
      (x.length+1)*(13*x.length.bits.length+15)+(x.map (price element)).sum ≤
      (shapeConstant element+100)*(wire (.list element) x).length*(B+1)
    nlinarith

end Maxwell.Cost.DecoderParser
