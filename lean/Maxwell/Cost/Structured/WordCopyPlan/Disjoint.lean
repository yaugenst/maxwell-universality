import Maxwell.Cost.Structured.WordCopyPlan

/-! A parallel copy plan is implemented by sequential charged copies when
its destination ports are distinct and disjoint from all source ports. -/
namespace Maxwell.Cost.Structured.WordCopyPlan

theorem evaluate_outside (plan : List (ℕ×ℕ)) (v : ℕ→List Bool) (i : ℕ)
    (outside : i∉targets plan) : evaluate plan v i=v i := by
  induction plan generalizing v with
  | nil => rfl
  | cons x rest ih =>
    have hi : i≠x.2 ∧ i∉targets rest := by
      simpa only [targets,List.map_cons,List.toFinset_cons,Finset.mem_insert,not_or] using outside
    exact (ih _ hi.2).trans (Function.update_of_ne hi.1 _ _)

theorem evaluate_copies (plan : List (ℕ×ℕ))
    (distinct : (plan.map Prod.snd).Nodup)
    (disjoint : ∀x∈plan,∀y∈plan,x.2≠y.1) (v : ℕ→List Bool) :
    ∀x∈plan,evaluate plan v x.2=v x.1 := by
  induction plan generalizing v with
  | nil => simp
  | cons x rest ih =>
    have hd := List.nodup_cons.mp distinct
    intro y hy
    rcases List.mem_cons.mp hy with hy|hy
    · subst y
      change evaluate rest (Function.update v x.2 (v x.1)) x.2=v x.1
      rw [evaluate_outside rest _ x.2 (by simpa only [targets,List.mem_toFinset] using hd.1),Function.update_self]
    · change evaluate rest (Function.update v x.2 (v x.1)) y.2=v y.1
      rw [ih hd.2 (fun a ha b hb=>disjoint a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
        _ y hy]
      exact Function.update_of_ne (Ne.symm (disjoint x (by simp) y (List.mem_cons_of_mem _ hy))) _ _

#print axioms evaluate_copies
end Maxwell.Cost.Structured.WordCopyPlan
