import Maxwell.Continuum.RationalDataflowTrace

namespace Maxwell.Continuum.RationalDataflow

theorem WidthTrace.result {S : Finset ℕ} {B : ℕ} {ins : List Instruction} {v : ℕ→Parts}
    (h : WidthTrace S B ins v) : WidthBank S B (evaluate ins v) := by
  induction ins generalizing v with
  | nil => exact h
  | cons a rest ih => exact ih h.2.2

end Maxwell.Continuum.RationalDataflow
