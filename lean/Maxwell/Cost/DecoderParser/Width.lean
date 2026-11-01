import Maxwell.Cost.DecoderParser.Bounds

namespace Maxwell.Cost.DecoderParser

theorem record_length_le {α : Type*} (f : α→List Bool) (xs : List α) (x : α) (hx : x∈xs) :
    (f x).length≤(xs.flatMap f).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl|hx
    · simp
    · have h := ih hx
      simp only [List.flatMap_cons,List.length_append]
      omega

/-- A local record's bit length bounds each binary field inside that record.
For a long stream, apply this to individual records and bound its outer count
separately; this avoids a quadratic bound in the number of records. -/
theorem widthBound_of_length (shape : Shape) (x : Payload shape) {B : ℕ}
    (h : (wire shape x).length≤B) : WidthBound shape x B := by
  induction shape with
  | bit => trivial
  | nat =>
    simp only [wire,Codec.nat,List.length_append,List.length_replicate,List.length_cons] at h
    exact (by change x.bits.length≤B;omega)
  | pair left right ihl ihr =>
    rcases x with ⟨x,y⟩
    simp only [wire,List.length_append] at h
    exact ⟨ihl x (by omega),ihr y (by omega)⟩
  | list element ih =>
    have hl : (x.flatMap (wire element)).length≤B := by
      simp only [wire,Codec.list,List.length_append] at h
      omega
    refine ⟨?_,fun y hy => ih y ((record_length_le (wire element) x y hy).trans hl)⟩
    simp only [wire,Codec.list,Codec.nat,List.length_append,List.length_replicate,List.length_cons] at h
    omega

#print axioms widthBound_of_length

end Maxwell.Cost.DecoderParser
