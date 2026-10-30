import Maxwell.Cost.Structured.Hoare

/-! Charged while loops whose natural-valued measure may decrease by more
than one. Every iteration still requires an actual machine execution. -/

namespace Maxwell.Cost.Structured

theorem loop_measure_bound
    (input : List Bool) (tape : ℕ→Bool) (register : ℕ) (body : Code)
    (invariant : Store→Prop) (measure : Store→ℕ) (cap : ℕ)
    (step : ∀s, invariant s → s.val.registers register=true →
      ∃cost t, Executes input tape body cost s t ∧ invariant t ∧
        measure t<measure s ∧ cost≤cap)
    (s : Store) (hs : invariant s) :
    ∃cost t, Executes input tape (.loop register body) cost s t ∧
      invariant t ∧ t.val.registers register=false ∧ cost≤1+measure s*(cap+1) := by
  suffices ∀n s, measure s=n → invariant s →
      ∃cost t, Executes input tape (.loop register body) cost s t ∧
        invariant t ∧ t.val.registers register=false ∧ cost≤1+n*(cap+1) from
    this (measure s) s rfl hs
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s hn hs
    cases ht : s.val.registers register with
    | false => exact ⟨1,s,Executes.done ht,hs,ht,by omega⟩
    | true =>
      obtain ⟨first,u,he,hu,hm,hc⟩ := step s hs ht
      obtain ⟨rest,t,et,hv,hfalse,hr⟩ := ih (measure u) (by omega) u rfl hu
      refine ⟨1+first+rest,t,Executes.more ht he et,hv,hfalse,?_⟩
      have hh := Nat.mul_le_mul_right (cap+1) (show measure u+1≤n by omega)
      nlinarith only [hc,hr,hh]

#print axioms loop_measure_bound

end Maxwell.Cost.Structured
