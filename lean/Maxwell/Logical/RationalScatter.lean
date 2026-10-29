import Maxwell.Logical.Routing.DummyFill

namespace Maxwell.Logical.RationalScatter

structure Update (d : ℕ) where
  address : Fin d
  increment : ℚ

def sumAt {d : ℕ} (updates : List (Update d)) (i : Fin d) : ℚ :=
  (updates.map (fun u => if u.address = i then u.increment else 0)).sum

def run {d : ℕ} : List (Update d) → Vector ℚ d → Vector ℚ d
  | [], saved => saved
  | u :: rest, saved => run rest
      (saved.set u.address.val (saved.get u.address + u.increment) u.address.isLt)

theorem run_get {d : ℕ} (updates : List (Update d)) (saved : Vector ℚ d) (i : Fin d) :
    (run updates saved).get i = saved.get i + sumAt updates i := by
  induction updates generalizing saved with
  | nil => simp [run, sumAt]
  | cons u rest ih =>
      rw [run, ih, Routing.DummyFill.get_set]
      by_cases h : u.address = i <;> simp [h, sumAt, add_assoc]

def materialize {d : ℕ} (updates : List (Update d)) : Vector ℚ d :=
  run updates (Vector.replicate d 0)

theorem materialize_get {d : ℕ} (updates : List (Update d)) (i : Fin d) :
    (materialize updates).get i = sumAt updates i := by
  rw [materialize, run_get]
  simp [Vector.get, Fin.cast]

@[simp] theorem sumAt_append {d : ℕ} (a b : List (Update d)) (i : Fin d) :
    sumAt (a ++ b) i = sumAt a i + sumAt b i := by simp [sumAt]

theorem sumAt_flatMap {d : ℕ} {α : Type*} (xs : List α) (f : α → List (Update d)) (i : Fin d) :
    sumAt (xs.flatMap f) i = (xs.map (fun x => sumAt (f x) i)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, ih]

end Maxwell.Logical.RationalScatter
