import Maxwell.Continuum.DefinitenessExpressions

/-! Semantics and raw-word traces for the fixed symbolic sign circuit. -/

namespace Maxwell.Continuum.Calibration.ExpressionDefiniteness

open RationalDataflow

theorem control_result {n : ℕ} (A : Matrix (Fin n) (Fin n) RationalExpression)
    (out s : ℕ) (hA : Below A s) (v : ℕ → Parts) :
    (control A out s).evaluate v out=Parts.literal (if RawDefiniteness.positive (evaluate A v) then 1 else 0) := by
  induction n generalizing v with
  | zero => exact result_evaluate out true v
  | succ n ih =>
    let w := RationalDataflow.evaluate ((A 0 0).instructions s) v
    have hframe : ∀ i<s, w i=v i := fun i hi =>
      (A 0 0).instructions_frame s v i (Or.inl hi)
    have hp : w ((A 0 0).output s)=(A 0 0).evaluate v :=
      (A 0 0).instructions_result s (hA 0 0) v
    have hschur : evaluate (schur A) w=RawDefiniteness.schur (evaluate A v) := by
      rw [evaluate_congr (schur A) (schur_below A hA) w v hframe,evaluate_schur]
    rw [control,Control.prepend_evaluate]
    change (if 0<(w ((A 0 0).output s)).value then (control (schur A) out s).evaluate w
      else (result out false).evaluate w) out=_
    rw [hp]
    by_cases hpos : 0<((A 0 0).evaluate v).value
    · rw [ite_eq_left hpos,ih (schur A) (schur_below A hA) w,hschur]
      change _=Parts.literal (if (if 0<((A 0 0).evaluate v).value then
        RawDefiniteness.positive (RawDefiniteness.schur (evaluate A v)) else false) then 1 else 0)
      rw [ite_eq_left hpos]
    · rw [ite_eq_right hpos,result_evaluate]
      change _=Parts.literal (if (if 0<((A 0 0).evaluate v).value then
        RawDefiniteness.positive (RawDefiniteness.schur (evaluate A v)) else false) then 1 else 0)
      rw [ite_eq_right hpos]

theorem control_admissible {n : ℕ} (A : Matrix (Fin n) (Fin n) RationalExpression)
    (out s : ℕ) (hA : Below A s) (v : ℕ → Parts) (hsafe : Safe A v) :
    (control A out s).AdmissibleTrace v := by
  induction n generalizing v with
  | zero => exact ⟨trivial,trivial⟩
  | succ n ih =>
    let w := RationalDataflow.evaluate ((A 0 0).instructions s) v
    have hframe : ∀ i<s, w i=v i := fun i hi =>
      (A 0 0).instructions_frame s v i (Or.inl hi)
    have hp : w ((A 0 0).output s)=(A 0 0).evaluate v :=
      (A 0 0).instructions_result s (hA 0 0) v
    rw [control]
    apply Control.prepend_admissibleTrace
    · exact (A 0 0).instructions_admissible s (hA 0 0) v (hsafe 0 0)
    · change if 0<(w ((A 0 0).output s)).value then
        (control (schur A) out s).AdmissibleTrace w else (result out false).AdmissibleTrace w
      rw [hp]
      by_cases hpos : 0<((A 0 0).evaluate v).value
      · rw [ite_eq_left hpos]
        apply ih (schur A) (schur_below A hA) w
        exact (safe_congr (schur A) (schur_below A hA) w v hframe).mpr
          (schur_safe A v hsafe hpos.ne')
      · rw [ite_eq_right hpos]
        exact ⟨trivial,trivial⟩

theorem control_widthTrace {n : ℕ} (A : Matrix (Fin n) (Fin n) RationalExpression)
    (out s : ℕ) (hA : Below A s) (S : Finset ℕ) (B W : ℕ)
    (hB : extent A*(W+1)≤B) (v : ℕ → Parts) (hv : WidthBank S B v)
    (hi : ∀ i<s, (v i).Width W) : (control A out s).WidthTrace S B v := by
  induction n generalizing v with
  | zero =>
    apply result_widthTrace out true S B _ v hv
    change 1*(W+1)≤B at hB
    omega
  | succ n ih =>
    let w := RationalDataflow.evaluate ((A 0 0).instructions s) v
    have hframe : ∀ i<s, w i=v i := fun i hi =>
      (A 0 0).instructions_frame s v i (Or.inl hi)
    have hpB : (A 0 0).nodes*(W+1)≤B :=
      (Nat.mul_le_mul_right (W+1) (le_max_left _ _)).trans hB
    have hsB : extent (schur A)*(W+1)≤B :=
      (Nat.mul_le_mul_right (W+1) (le_max_right _ _)).trans hB
    have hnode := ((A 0 0).nodeWidths s W (hA 0 0) v hi).mono hpB
    have htrace := (A 0 0).instructions_widthTrace s (hA 0 0) S B v hv hnode
    have hw : WidthBank S B w := RationalExpression.widthTrace_final S B _ v htrace
    rw [control]
    apply Control.prepend_widthTrace S _ _ v B htrace
    change WidthBank S B w ∧ if 0<(w ((A 0 0).output s)).value then
      (control (schur A) out s).WidthTrace S B w else (result out false).WidthTrace S B w
    refine ⟨hw,?_⟩
    split_ifs
    · apply ih (schur A) (schur_below A hA) hsB w hw
      intro i hlt
      rw [hframe i hlt]
      exact hi i hlt
    · apply result_widthTrace out false S B _ w hw
      have h1 : 1≤extent A := extent_pos A
      have h2 := Nat.mul_le_mul_right (W+1) h1
      omega

#print axioms control_result
#print axioms control_admissible
#print axioms control_widthTrace

end Maxwell.Continuum.Calibration.ExpressionDefiniteness
