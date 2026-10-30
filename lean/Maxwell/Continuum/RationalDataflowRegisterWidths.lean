import Maxwell.Continuum.RationalDataflowControlResults

/-! Executable register-wise raw-width inference.  Unlike a repeated
uniform doubling estimate, it records which cached inputs each output
actually uses, including the additive accumulator in tensor contraction. -/

namespace Maxwell.Continuum.RationalDataflow
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def Instruction.resultWidth (a : Instruction) (w : ℕ→ℕ) : ℕ :=
  match a with
  | .literal _ q => max (Parts.literal q).positive.bits.length
      (max (Parts.literal q).negative.bits.length (Parts.literal q).denominator.bits.length)
  | .binary _ _ left right => w left+w right+1
  | .inverse _ source => w source+1

def Instruction.widthUpdate (a : Instruction) (w : ℕ→ℕ) : ℕ→ℕ :=
  match a with
  | .literal target _ | .binary _ target _ _ | .inverse target _ =>
      Function.update w target (a.resultWidth w)

def RegisterWidths (S : Finset ℕ) (w : ℕ→ℕ) (v : ℕ→Parts) : Prop :=
  ∀i∈S,(v i).Width (w i)

theorem Instruction.update_registerWidths (S : Finset ℕ) (a : Instruction) (ha : a.Valid S)
    (w : ℕ→ℕ) (v : ℕ→Parts) (hv : RegisterWidths S w v) :
    RegisterWidths S (a.widthUpdate w) (a.update v) := by
  intro i hi
  cases a with
  | literal target q =>
    by_cases he : i=target
    · subst i
      simp only [Instruction.update,Instruction.widthUpdate,Instruction.resultWidth,Function.update_self]
      exact ⟨le_max_left _ _,(le_max_left _ _).trans (le_max_right _ _),
        (le_max_right _ _).trans (le_max_right _ _)⟩
    · simpa only [Instruction.update,Instruction.widthUpdate,Function.update_of_ne he] using hv i hi
  | binary op target left right =>
    by_cases he : i=target
    · subst i
      simp only [Instruction.update,Instruction.widthUpdate,Instruction.resultWidth,Function.update_self]
      cases op
      · exact (hv left ha.2.1).add (hv right ha.2.2)
      · exact (hv left ha.2.1).sub (hv right ha.2.2)
      · exact (hv left ha.2.1).mul (hv right ha.2.2)
    · simpa only [Instruction.update,Instruction.widthUpdate,Function.update_of_ne he] using hv i hi
  | inverse target source =>
    by_cases he : i=target
    · subst i
      simpa only [Instruction.update,Instruction.widthUpdate,Instruction.resultWidth,
        Function.update_self] using (hv source ha.2).inverse
    · simpa only [Instruction.update,Instruction.widthUpdate,Function.update_of_ne he] using hv i hi

def programWidth : List Instruction → (ℕ→ℕ) → ℕ
  | [],_ => 0
  | a::rest,w => max (a.resultWidth w) (programWidth rest (a.widthUpdate w))

theorem inferred_widthTrace (S : Finset ℕ) (ins : List Instruction)
    (ha : ∀a∈ins,a.Valid S) (w : ℕ→ℕ) (v : ℕ→Parts)
    (hv : RegisterWidths S w v) (B : ℕ) (hbank : WidthBank S B v)
    (hp : programWidth ins w≤B) : WidthTrace S B ins v := by
  induction ins generalizing v w with
  | nil => exact hbank
  | cons a rest ih =>
    have hleft : a.resultWidth w≤B := (le_max_left _ _).trans hp
    have hright : programWidth rest (a.widthUpdate w)≤B := (le_max_right _ _).trans hp
    have hav := ha a (by simp)
    have hnext := a.update_registerWidths S hav w v hv
    have hnew : WidthBank S B (a.update v) := by
      intro i hi
      cases a with
      | literal target q =>
        by_cases he : i=target
        · subst i
          exact (hnext target hi).mono (by simpa only [Instruction.widthUpdate,Function.update_self] using hleft)
        · simpa only [Instruction.update,Function.update_of_ne he] using hbank i hi
      | binary op target left right =>
        by_cases he : i=target
        · subst i
          exact (hnext target hi).mono (by simpa only [Instruction.widthUpdate,Function.update_self] using hleft)
        · simpa only [Instruction.update,Function.update_of_ne he] using hbank i hi
      | inverse target source =>
        by_cases he : i=target
        · subst i
          exact (hnext target hi).mono (by simpa only [Instruction.widthUpdate,Function.update_self] using hleft)
        · simpa only [Instruction.update,Function.update_of_ne he] using hbank i hi
    refine ⟨hbank,?_,ih (fun b hb => ha b (by simp [hb])) (a.widthUpdate w) (a.update v) hnext hnew hright⟩
    cases a with
    | literal target q =>
      exact ⟨(le_max_left _ _).trans hleft,
        ((le_max_left _ _).trans (le_max_right _ _)).trans hleft,
        ((le_max_right _ _).trans (le_max_right _ _)).trans hleft⟩
    | binary => trivial
    | inverse => trivial

#print axioms inferred_widthTrace
end Maxwell.Continuum.RationalDataflow
