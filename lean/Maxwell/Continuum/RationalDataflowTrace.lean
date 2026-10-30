import Maxwell.Continuum.RationalDataflowControl

/-! Small shared-bank and trace joins for arithmetic recipes. -/

namespace Maxwell.Continuum.RationalDataflow
set_option maxHeartbeats 1000000

theorem WidthBank.update {S : Finset ℕ} {B : ℕ} {v : ℕ→Parts} (hv : WidthBank S B v)
    (target : ℕ) {x : Parts} (hx : x.Width B) : WidthBank S B (Function.update v target x) := by
  intro i hi
  by_cases he : i=target
  · subst i; simpa only [Function.update_self] using hx
  · simpa only [Function.update_of_ne he] using hv i hi

theorem Good.update {S : Finset ℕ} {v : ℕ→Parts} (hv : Good S v)
    (target : ℕ) {x : Parts} (hx : x.Valid) : Good S (Function.update v target x) := by
  intro i hi
  by_cases he : i=target
  · subst i; simpa only [Function.update_self] using hx
  · simpa only [Function.update_of_ne he] using hv i hi

theorem WidthBank.mono {S : Finset ℕ} {B C : ℕ} {v : ℕ→Parts} (hv : WidthBank S B v)
    (hBC : B≤C) : WidthBank S C v := fun i hi => (hv i hi).mono hBC

theorem WidthTrace.mono (S : Finset ℕ) (ins : List Instruction) (v : ℕ→Parts) (B C : ℕ)
    (hBC : B≤C) (hw : WidthTrace S B ins v) : WidthTrace S C ins v := by
  induction ins generalizing v with
  | nil => exact WidthBank.mono hw hBC
  | cons a rest ih =>
    refine ⟨WidthBank.mono hw.1 hBC,?_,ih (a.update v) hw.2.2⟩
    cases a
    · exact Parts.Width.mono hw.2.1 hBC
    · trivial
    · trivial

theorem Control.prepend_valid (S : Finset ℕ) (ins : List Instruction) (tail : Control)
    (hins : ∀ a∈ins, a.Valid S) (htail : tail.Valid S) : (tail.prepend ins).Valid S := by
  induction ins with
  | nil => exact htail
  | cons a rest ih => exact ⟨hins a (by simp),ih (fun b hb => hins b (by simp [hb]))⟩

theorem Control.prepend_widthTrace (S : Finset ℕ) (ins : List Instruction) (tail : Control)
    (v : ℕ→Parts) (B : ℕ) (hins : RationalDataflow.WidthTrace S B ins v)
    (htail : tail.WidthTrace S B (RationalDataflow.evaluate ins v)) :
    (tail.prepend ins).WidthTrace S B v := by
  induction ins generalizing v with
  | nil => exact htail
  | cons a rest ih => exact ⟨hins.1,hins.2.1,ih (a.update v) hins.2.2 htail⟩

theorem Control.prepend_admissibleTrace (ins : List Instruction) (tail : Control)
    (v : ℕ→Parts) (hins : RationalDataflow.AdmissibleTrace ins v)
    (htail : tail.AdmissibleTrace (RationalDataflow.evaluate ins v)) :
    (tail.prepend ins).AdmissibleTrace v := by
  induction ins generalizing v with
  | nil => exact htail
  | cons a rest ih => exact ⟨hins.1,ih (a.update v) hins.2 htail⟩

#print axioms Control.prepend_widthTrace

end Maxwell.Continuum.RationalDataflow
