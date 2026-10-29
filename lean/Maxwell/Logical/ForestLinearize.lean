import Maxwell.Logical.Forest
import Maxwell.Logical.Linearize

namespace Maxwell.Logical

def forestLeafCount {n : ℕ} : List (Expression n) → ℕ
  | [] => 0
  | e :: es => e.leafCount + forestLeafCount es

def forestSources {n : ℕ} : (rows : List (Expression n)) → Fin (forestLeafCount rows) → Fin n
  | [] => Fin.elim0
  | e :: es => Fin.append e.leafSource (forestSources es)

def linearizedRows {n : ℕ} : (rows : List (Expression n)) → List (Expression (forestLeafCount rows))
  | [] => []
  | e :: es => e.linearized.rename (Fin.castAdd (forestLeafCount es)) ::
      (linearizedRows es).map (Expression.rename (Fin.natAdd e.leafCount))

theorem forestSources_list {n : ℕ} (rows : List (Expression n)) :
    List.ofFn (forestSources rows) = (rows.map Expression.occurrences).flatten := by
  induction rows with
  | nil => rfl
  | cons e es ih =>
      change List.ofFn (Fin.append e.leafSource (forestSources es)) =
        e.occurrences ++ (es.map Expression.occurrences).flatten
      rw [List.ofFn_fin_append, e.leafSource_list, ih]

theorem forestLeafCount_eq_sum {n : ℕ} (rows : List (Expression n)) :
    forestLeafCount rows = (rows.map Expression.leafCount).sum := by
  induction rows with
  | nil => rfl
  | cons e es ih => simp [forestLeafCount, ih]

theorem linearizedRows_gateCounts {n : ℕ} (rows : List (Expression n)) :
    (linearizedRows rows).map Expression.gateCount = rows.map Expression.gateCount := by
  induction rows with
  | nil => rfl
  | cons e es ih =>
      dsimp only [linearizedRows, forestLeafCount]
      simp only [List.map_cons, List.map_map, Function.comp_def, Expression.rename_gateCount,
        Expression.linearized_gateCount]
      exact congrArg (List.cons e.gateCount) ih

theorem linearizedRows_evaluate {n : ℕ} (rows : List (Expression n)) (input : Fin n → ℝ) :
    (linearizedRows rows).map (fun e => e.evaluate (fun i => input (forestSources rows i))) =
      rows.map (fun e => e.evaluate input) := by
  induction rows with
  | nil => rfl
  | cons e es ih =>
      dsimp only [linearizedRows, forestSources, forestLeafCount]
      simp only [List.map_cons, List.map_map, Expression.rename_evaluate,
        Function.comp_def, Fin.append_left, Fin.append_right, Expression.linearized_evaluate]
      exact congrArg (List.cons (e.evaluate input)) ih

theorem linearizedRows_bounded {n : ℕ} (rows : List (Expression n))
    (h : ∀ e ∈ rows, e.BoundedWeights) :
    ∀ e ∈ linearizedRows rows, e.BoundedWeights := by
  induction rows with
  | nil => simp [linearizedRows]
  | cons e es ih =>
      intro a ha
      dsimp only [linearizedRows, forestLeafCount] at ha
      rcases List.mem_cons.mp ha with he | he
      · subst a
        exact (Expression.rename_bounded _ _).2 ((e.linearized_bounded).2 (h e (by simp)))
      · rcases List.mem_map.mp he with ⟨b, hb, hab⟩
        rw [← hab]
        exact (Expression.rename_bounded _ _).2 (ih (fun c hc => h c (by simp [hc])) b hb)

theorem linearizedRows_occurrences {n : ℕ} (rows : List (Expression n)) :
    ((linearizedRows rows).map Expression.occurrences).flatten =
      List.finRange (forestLeafCount rows) := by
  induction rows with
  | nil => rfl
  | cons e es ih =>
      dsimp only [linearizedRows, forestLeafCount]
      simp only [List.map_cons, List.flatten_cons, List.map_map, Expression.occurrences_rename,
        Expression.linearized_occurrences, Function.comp_def]
      have hm : List.map (fun a : Expression (forestLeafCount es) =>
          a.occurrences.map (Fin.natAdd e.leafCount)) (linearizedRows es) =
          List.map (List.map (Fin.natAdd e.leafCount))
            ((linearizedRows es).map Expression.occurrences) := by
        rw [List.map_map]
        rfl
      rw [hm, ← List.map_flatten, ih, ← List.ofFn_eq_map, ← List.ofFn_eq_map,
        ← List.ofFn_fin_append]
      have hf : Fin.append (Fin.castAdd (forestLeafCount es)) (Fin.natAdd e.leafCount) = id := by
        funext i
        exact Fin.addCases (fun j => by simp) (fun j => by simp) i
      rw [hf]
      exact List.ofFn_id _

end Maxwell.Logical
