import Maxwell.Continuum.RationalDataflowControlResults

/-! Composition of fixed rational control fragments. The continuation is
inserted at each terminal branch; no runtime integer changes the code. -/

namespace Maxwell.Continuum.RationalDataflow

def Control.andThen : Control → Control → Control
  | .done, next => next
  | .step a rest, next => .step a (rest.andThen next)
  | .positive source yes no, next =>
      .positive source (yes.andThen next) (no.andThen next)

theorem Control.andThen_evaluate (c next : Control) (v : ℕ → Parts) :
    (c.andThen next).evaluate v=next.evaluate (c.evaluate v) := by
  induction c generalizing v with
  | done => rfl
  | step a rest ih => exact ih (a.update v)
  | positive source yes no iy ino =>
    simp only [andThen,evaluate]
    split_ifs <;> simp only [iy,ino]

theorem Control.andThen_valid (c next : Control) (S : Finset ℕ)
    (hc : c.Valid S) (hn : next.Valid S) : (c.andThen next).Valid S := by
  induction c with
  | done => exact hn
  | step a rest ih => exact ⟨hc.1,ih hc.2⟩
  | positive source yes no iy ino => exact ⟨hc.1,iy hc.2.1,ino hc.2.2⟩

theorem Control.andThen_admissible (c next : Control) (v : ℕ → Parts)
    (hc : c.AdmissibleTrace v) (hn : next.AdmissibleTrace (c.evaluate v)) :
    (c.andThen next).AdmissibleTrace v := by
  induction c generalizing v with
  | done => exact hn
  | step a rest ih => exact ⟨hc.1,ih (a.update v) hc.2 hn⟩
  | positive source yes no iy ino =>
    by_cases hp : 0<(v source).value
    · simpa only [andThen,AdmissibleTrace,hp,ite_true] using iy v
        (by simpa only [AdmissibleTrace,hp,ite_true] using hc)
        (by simpa only [evaluate,hp,ite_true] using hn)
    · simpa only [andThen,AdmissibleTrace,hp,ite_false] using ino v
        (by simpa only [AdmissibleTrace,hp,ite_false] using hc)
        (by simpa only [evaluate,hp,ite_false] using hn)

theorem Control.andThen_steps (c next : Control) :
    (c.andThen next).steps=c.steps+next.steps := by
  induction c with
  | done => simp [andThen,steps]
  | step a rest ih => simp only [andThen,steps,ih]; omega
  | positive source yes no iy ino => simp only [andThen,steps,iy,ino]; omega

theorem Control.andThen_literals (c next : Control) (W : ℕ)
    (hc : c.LiteralsFit W) (hn : next.LiteralsFit W) :
    (c.andThen next).LiteralsFit W := by
  induction c with
  | done => exact hn
  | step a rest ih => exact ⟨hc.1,ih hc.2⟩
  | positive source yes no iy ino => exact ⟨iy hc.1,ino hc.2⟩

#print axioms Control.andThen_admissible

end Maxwell.Continuum.RationalDataflow
