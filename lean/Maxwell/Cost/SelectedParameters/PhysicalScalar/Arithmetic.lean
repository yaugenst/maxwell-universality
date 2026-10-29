import Maxwell.Cost.SelectedParameters.RationalScript

namespace Maxwell.Cost.SelectedParameters.PhysicalScalar
open RationalScript Rational
set_option maxHeartbeats 1500000

/-- A pair of actual stored unsigned words represents this rational. -/
def HasValue (v : ℕ → ℕ) (port : ℕ) (q : ℚ) : Prop :=
  0 < v (port+1) ∧ (v port : ℚ)/v (port+1) = q

def literal (port n d : ℕ) : RationalScript.Instruction := ⟨.literal n d,port,port+1⟩
def basic (op : Basic) (port a b : ℕ) : RationalScript.Instruction := ⟨.basic op a (a+1) b (b+1),port,port+1⟩
def choice (op : Choice) (port a b : ℕ) : RationalScript.Instruction := ⟨.choice op a (a+1) b (b+1),port,port+1⟩
def power (port k a : ℕ) : RationalScript.Instruction := ⟨.power k a (a+1),port,port+1⟩

theorem HasValue.nonneg {v : ℕ → ℕ} {port : ℕ} {q : ℚ} (h : HasValue v port q) : 0 ≤ q := by
  rw [← h.2]
  positivity

theorem HasValue.numerator_pos {v : ℕ → ℕ} {port : ℕ} {q : ℚ}
    (h : HasValue v port q) (hq : 0 < q) : 0 < v port := by
  by_contra hh
  have hz : v port = 0 := by omega
  simp [HasValue,hz] at h
  linarith [h.2]

theorem HasValue.clean {v : ℕ → ℕ} {port : ℕ} {q : ℚ}
    (h : HasValue v port q) (hp : 540 ≤ port) : HasValue (Rational.clean v) port q := by
  have h0 : port ∉ common := by simp only [common,Finset.mem_insert,Finset.mem_singleton]; omega
  have h1 : port+1 ∉ common := by simp only [common,Finset.mem_insert,Finset.mem_singleton]; omega
  simpa only [HasValue,clean_apply,ite_eq_right h0,ite_eq_right h1] using h

@[simp] theorem hasValue_update_keep (a : RationalScript.Instruction) (v : ℕ → ℕ) (port : ℕ) (q : ℚ)
    (hp : 540 ≤ port) (h0 : port ≠ a.numerator) (h1 : port ≠ a.denominator)
    (h2 : port+1 ≠ a.numerator) (h3 : port+1 ≠ a.denominator) :
    HasValue (a.update v) port q ↔ HasValue v port q := by
  have hnot : port ∉ common := by simp only [common,Finset.mem_insert,Finset.mem_singleton]; omega
  have hnot' : port+1 ∉ common := by simp only [common,Finset.mem_insert,Finset.mem_singleton]; omega
  simp only [HasValue,RationalScript.Instruction.update,after_other _ _ _ _ _ hnot h0 h1,
    after_other _ _ _ _ _ hnot' h2 h3]

theorem hasValue_written (a : RationalScript.Instruction) (v : ℕ → ℕ) (port : ℕ) (q : ℚ)
    (hp : 540 ≤ port) (hn : a.numerator=port) (hd : a.denominator=port+1)
    (hden : 0 < (a.result v).2) (hvalue : value (a.result v)=q) :
    HasValue (a.update v) port q := by
  simpa only [HasValue,value,RationalScript.Instruction.update,hn,hd,
    after_num _ _ _ _ hp (by omega : port≠port+1),
    after_den _ _ _ _ (by omega : 540≤port+1)] using And.intro hden hvalue

theorem literal_value (v : ℕ → ℕ) (port n d : ℕ) (hp : 540 ≤ port) (hd : 0 < d) :
    HasValue ((literal port n d).update v) port ((n:ℚ)/d) :=
  hasValue_written _ _ _ _ hp rfl rfl hd rfl

theorem basic_value (v : ℕ → ℕ) (op : Basic) (port a b : ℕ) (x y : ℚ)
    (hp : 540 ≤ port) (hx : HasValue v a x) (hy : HasValue v b y)
    (hdiv : op=.divide → 0 < y) :
    HasValue ((basic op port a b).update v) port (evaluate op x y) := by
  have hv : Rational.Valid op (v (a+1)) (v b) (v (b+1)) :=
    ⟨hx.1,hy.1,fun h => hy.numerator_pos (hdiv h)⟩
  apply hasValue_written _ _ _ _ hp rfl rfl
  · exact pair_denominator op _ _ _ _ hv
  · simpa only [basic,RationalScript.Instruction.result,hx.2,hy.2] using pair_value op (v a) (v (a+1)) (v b) (v (b+1)) hv

theorem choice_value (v : ℕ → ℕ) (op : Choice) (port a b : ℕ) (x y : ℚ)
    (hp : 540 ≤ port) (hx : HasValue v a x) (hy : HasValue v b y) :
    HasValue ((choice op port a b).update v) port (choiceValue op x y) := by
  apply hasValue_written _ _ _ _ hp rfl rfl
  · exact choice_denominator op _ _ _ _ hx.1 hy.1
  · simpa only [choice,RationalScript.Instruction.result,hx.2,hy.2] using Rational.choice_value op (v a) (v (a+1)) (v b) (v (b+1))

theorem power_value (v : ℕ → ℕ) (port k a : ℕ) (x : ℚ)
    (hp : 540 ≤ port) (hx : HasValue v a x) :
    HasValue ((power port k a).update v) port (x^k) := by
  apply hasValue_written _ _ _ _ hp rfl rfl
  · exact power_denominator k _ _ hx.1
  · simpa only [power,RationalScript.Instruction.result,hx.2] using Rational.power_value k (v a) (v (a+1))

end Maxwell.Cost.SelectedParameters.PhysicalScalar
