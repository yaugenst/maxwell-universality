import Maxwell.Continuum.RationalDataflowProgram

/-! Exact finite register widths for arbitrary unreduced rational parts.
Resource bounds can be proved separately from the semantic representation. -/
namespace Maxwell.Continuum.RationalDataflow

def Parts.bitWidth (x : Parts) : ℕ :=
  max x.positive.bits.length (max x.negative.bits.length x.denominator.bits.length)

theorem Parts.width_bitWidth (x : Parts) : x.Width x.bitWidth :=
  ⟨le_max_left _ _,(le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

def bankWidth (bank : Finset ℕ) (values : ℕ→Parts) : ℕ :=
  bank.sup (fun i=>(values i).bitWidth)

theorem widthBank_bankWidth (bank : Finset ℕ) (values : ℕ→Parts) :
    WidthBank bank (bankWidth bank values) values := by
  intro i hi
  exact (Parts.width_bitWidth (values i)).mono (Finset.le_sup (f:=fun k=>(values k).bitWidth) hi)

#print axioms widthBank_bankWidth
end Maxwell.Continuum.RationalDataflow
