import Maxwell.Cost.SelectedParameters.RationalChoice
import Maxwell.Cost.SelectedParameters.RationalPower

/-! Actual finite-code rational addition, multiplication, division, minimum,
maximum and fixed natural powers. The execution theorems describe canonical
stored natural numerator/denominator words; the value lemmas establish their
exact rational meanings. Results may remain unreduced. All operations restore
the shared arithmetic bank, and their charged costs are quadratic in the
input word width for each fixed program. -/
