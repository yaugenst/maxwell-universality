import Maxwell.Certificate.IntervalMatrix
namespace Maxwell.Certificate.IntervalMatrix

theorem subsetCheck_of_rows {n : ℕ} (a b : Enclosure n)
    (h : ∀ i j, Trigonometric.rectangleSubsetCheck (a i j) (b i j) = true) :
    subsetCheck a b = true := decide_eq_true h

end Maxwell.Certificate.IntervalMatrix
