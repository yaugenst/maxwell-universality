import Maxwell.Cost.Structured.Hoare

/-! A decreasing logical index can track a fixed machine loop without
adding a runtime rank oracle or a host callback to the program. -/

namespace Maxwell.Cost.Structured

theorem loop_indexed_measure_bound {α : Type*}
    (input : List Bool) (tape : ℕ→Bool) (register : ℕ) (body : Code)
    (invariant : α→Store→Prop) (measure : α→ℕ) (cap : ℕ)
    (step : ∀a s, invariant a s → s.val.registers register=true →
      ∃cost b t, Executes input tape body cost s t ∧ invariant b t ∧
        measure b<measure a ∧ cost≤cap)
    (a : α) (s : Store) (hs : invariant a s) :
    ∃cost b t, Executes input tape (.loop register body) cost s t ∧
      invariant b t ∧ t.val.registers register=false ∧ cost≤1+measure a*(cap+1) := by
  suffices ∀n a s, measure a=n → invariant a s →
      ∃cost b t, Executes input tape (.loop register body) cost s t ∧
        invariant b t ∧ t.val.registers register=false ∧ cost≤1+n*(cap+1) from
    this (measure a) a s rfl hs
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a s hn hs
    cases ht : s.val.registers register with
    | false => exact ⟨1,a,s,Executes.done ht,hs,ht,by omega⟩
    | true =>
      obtain ⟨first,b,u,he,hu,hm,hc⟩ := step a s hs ht
      obtain ⟨rest,c,t,et,hv,hfalse,hr⟩ := ih (measure b) (by omega) b u rfl hu
      refine ⟨1+first+rest,c,t,Executes.more ht he et,hv,hfalse,?_⟩
      have hh := Nat.mul_le_mul_right (cap+1) (show measure b+1≤n by omega)
      nlinarith only [hc,hr,hh]

#print axioms loop_indexed_measure_bound

end Maxwell.Cost.Structured
