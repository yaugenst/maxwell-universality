import Maxwell.Continuum.RationalDataflowFixedWidths

namespace Maxwell.Continuum.RationalDataflow

theorem Control.WidthTrace.result {c : Control} {S : Finset ℕ} {B : ℕ} {v : ℕ→Parts}
    (h : c.WidthTrace S B v) : WidthBank S B (c.evaluate v) := by
  induction c generalizing v with
  | done => exact h
  | step a rest ih => exact ih h.2.2
  | positive source yes no iy ino =>
    by_cases hp : 0<(v source).value
    · simpa only [Control.evaluate,hp,ite_true] using
        iy (by simpa only [Control.WidthTrace,hp,ite_true] using h.2)
    · simpa only [Control.evaluate,hp,ite_false] using
        ino (by simpa only [Control.WidthTrace,hp,ite_false] using h.2)

#print axioms Control.WidthTrace.result
end Maxwell.Continuum.RationalDataflow
