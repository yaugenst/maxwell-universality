import Maxwell.Cost.RealSimulation.IndexWidth

namespace Maxwell.Cost.RealSimulation

/-- Actual execution with a predicate checked at every visited state,
including both endpoints. This is stronger than an endpoint bound. -/
inductive VisitedSteps (next : RAMState → Option RAMState) (P : RAMState → Prop) :
    ℕ → RAMState → RAMState → Prop where
  | refl {s : RAMState} (holds : P s) : VisitedSteps next P 0 s s
  | step {n : ℕ} {s t u : RAMState} (holds : P s) (transition : next s = some t)
      (rest : VisitedSteps next P n t u) : VisitedSteps next P (n + 1) s u

theorem VisitedSteps.steps {next : RAMState → Option RAMState} {P : RAMState → Prop}
    {n : ℕ} {s t : RAMState} (h : VisitedSteps next P n s t) : Steps next n s t := by
  induction h with
  | refl => exact Steps.refl _
  | step _ h _ ih => exact Steps.step h ih

theorem VisitedSteps.start {next : RAMState → Option RAMState} {P : RAMState → Prop}
    {n : ℕ} {s t : RAMState} (h : VisitedSteps next P n s t) : P s := by
  cases h <;> assumption

theorem VisitedSteps.prefix {next : RAMState → Option RAMState} {P : RAMState → Prop}
    {n k : ℕ} {s t u : RAMState} (h : VisitedSteps next P n s t)
    (hk : k ≤ n) (tracePrefix : Steps next k s u) : P u := by
  induction h generalizing k u with
  | refl hs =>
    have hk : k = 0 := by omega
    subst k
    cases tracePrefix
    exact hs
  | @step n s t v hs hn rest ih =>
    cases tracePrefix with
    | refl => exact hs
    | @step k _ w _ hw hp =>
      have he : w = t := Option.some.inj (hw.symm.trans hn)
      subst w
      exact ih (by omega) hp

theorem VisitedSteps.mono {next : RAMState → Option RAMState} {P Q : RAMState → Prop}
    {n : ℕ} {s t : RAMState} (h : VisitedSteps next P n s t) (imp : ∀ u, P u → Q u) :
    VisitedSteps next Q n s t := by
  induction h with
  | refl hs => exact .refl (imp _ hs)
  | step hs hn _ ih => exact .step (imp _ hs) hn ih

theorem VisitedSteps.trans {next : RAMState → Option RAMState} {P : RAMState → Prop}
    {n m : ℕ} {s t u : RAMState}
    (h : VisitedSteps next P n s t) (k : VisitedSteps next P m t u) :
    VisitedSteps next P (n + m) s u := by
  induction h with
  | refl => simpa using k
  | step hs hn _ ih => simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      VisitedSteps.step hs hn (ih k)

theorem visited_index_bound {M : Machine} {input : RAMInput} {tape : ℕ → Bool}
    {B K k : ℕ} {s t : RAMState} (hs : IndexWidth.IndexBound B s)
    (hc : IndexWidth.LiteralBound K M) (hi : IndexWidth.InputBound K input) (hKB : K ≤ B)
    (h : Steps (M.next input tape) k s t) :
    VisitedSteps (M.next input tape) (IndexWidth.IndexBound (2 ^ k * B)) k s t := by
  induction h generalizing B with
  | refl s => simpa using VisitedSteps.refl hs
  | @step n s t u hn rest ih =>
    have ht : IndexWidth.IndexBound (2 * B) t := by
      simpa only [max_eq_left hKB] using IndexWidth.next_bound hs hc hi hn
    have hu := ih ht (show K ≤ 2 * B by omega)
    have he : 2 ^ n * (2 * B) = 2 ^ (n + 1) * B := by rw [pow_succ]; ring
    rw [he] at hu
    apply VisitedSteps.step (next := M.next input tape) (transition := hn) (rest := hu)
    apply hs.mono
    have hp : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow _ _ (by decide)
    nlinarith

def IndexWordWidth (width : ℕ) (s : RAMState) : Prop := ∀ j, (s.indices j).size ≤ width

theorem visited_segment_width {M : Machine} {input : RAMInput} {tape : ℕ → Bool}
    {W C k : ℕ} {s t : RAMState} (hs : IndexWidth.IndexBound (2 ^ W) s)
    (hc : IndexWidth.LiteralBound (2 ^ W) M) (hi : IndexWidth.InputBound (2 ^ W) input)
    (hcost : k ≤ C * (W + 1)) (h : Steps (M.next input tape) k s t) :
    VisitedSteps (M.next input tape) (IndexWordWidth ((C + 1) * (W + 1))) k s t := by
  apply (visited_index_bound hs hc hi le_rfl h).mono
  intro u hu j
  have hb := hu j
  rw [← pow_add] at hb
  have hw := Nat.size_le_size hb
  rw [Nat.size_pow] at hw
  nlinarith

end Maxwell.Cost.RealSimulation
