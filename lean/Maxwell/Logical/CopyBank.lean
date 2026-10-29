import Maxwell.Logical.CopyTree
import Maxwell.Logical.CopyOnly

namespace Maxwell.Logical

@[simp] theorem Circuit.copyGate_old {n d : ℕ} (c : Circuit n d) (parent i : Fin d)
    (input : Fin n → ℝ) (error : Fin (d + 1) → ℝ) :
    (c.copyGate parent).evaluate input error i.castSucc =
      c.evaluate input (fun j => error j.castSucc) i :=
  c.evaluate_append_castSucc _ input error i

/-- One unused root per original input. Splitting a root exposes one fresh
occurrence and retains one unused root for any later occurrences. -/
structure CopyBank (n : ℕ) where
  size : ℕ
  circuit : Circuit n size
  copy_only : circuit.CopyOnly
  root : Fin n → Fin size
  root_injective : Function.Injective root
  root_unused : ∀ i, circuit.uses (root i) = 0
  root_correct : ∀ (input : Fin n → ℝ) i, circuit.evaluate input 0 (root i) = input i
  uses_bound : ∀ j, circuit.uses j ≤ 2

namespace CopyBank

def initial (n : ℕ) : CopyBank n where
  size := n
  circuit := .input
  copy_only := .input
  root := id
  root_injective := Function.injective_id
  root_unused := by intro i; rfl
  root_correct := by intro input i; simp
  uses_bound := by intro j; simp

def splitRoot {n : ℕ} (bank : CopyBank n) (i : Fin n) : CopyBank n := by
  let c := (bank.circuit.copyGate (bank.root i)).copyGate (bank.root i).castSucc
  let root : Fin n → Fin (bank.size + 2) := fun j =>
    if j = i then Fin.last (bank.size + 1) else (bank.root j).castSucc.castSucc
  have old_ne_new (j : Fin bank.size) : j.castSucc.castSucc ≠ Fin.last (bank.size + 1) := by
    intro h
    have hv := congrArg (fun k : Fin (bank.size + 2) => k.val) h
    have hj := j.isLt
    simp only [Fin.val_castSucc, Fin.val_last] at hv
    omega
  have old_ne_first (j : Fin bank.size) : j.castSucc ≠ Fin.last bank.size := by
    intro h
    have hv := congrArg (fun k : Fin (bank.size + 1) => k.val) h
    have hj := j.isLt
    simp only [Fin.val_castSucc, Fin.val_last] at hv
    omega
  refine {
    size := bank.size + 2
    circuit := c
    copy_only := .copy (.copy bank.copy_only _) _
    root := root
    root_injective := ?_
    root_unused := ?_
    root_correct := ?_
    uses_bound := ?_ }
  · intro a b h
    by_cases ha : a = i
    · by_cases hb : b = i
      · exact ha.trans hb.symm
      · simp only [root, ha, hb, ↓reduceIte] at h
        exact False.elim (old_ne_new (bank.root b) h.symm)
    · by_cases hb : b = i
      · simp only [root, ha, hb, ↓reduceIte] at h
        exact False.elim (old_ne_new (bank.root a) h)
      · simp only [root, ha, hb, ↓reduceIte] at h
        apply bank.root_injective
        exact Fin.ext (congrArg (fun k : Fin (bank.size + 2) => k.val) h)
  · intro j
    by_cases hj : j = i
    · simp [root, hj, c]
    · have hroot : bank.root j ≠ bank.root i := fun h => hj (bank.root_injective h)
      have hcast : (bank.root j).castSucc ≠ (bank.root i).castSucc := by
        intro h
        exact hroot (Fin.ext (congrArg (fun k : Fin (bank.size + 1) => k.val) h))
      simp [root, hj, c, hroot, hcast, bank.root_unused]
  · intro input j
    by_cases hj : j = i
    · subst j
      simp only [root, ↓reduceIte, c, Circuit.copyGate_last, Circuit.copyGate_old,
        Pi.zero_apply, add_zero]
      exact bank.root_correct input i
    · simp only [root, hj, ↓reduceIte, c, Circuit.copyGate_old]
      exact bank.root_correct input j
  · intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [c]
    · refine Fin.lastCases ?_ (fun l => ?_) k
      · have hne := (old_ne_first (bank.root i)).symm
        simp [c, hne]
      · by_cases hl : l = bank.root i
        · subst l
          simp [c, bank.root_unused]
        · have hcast : l.castSucc ≠ (bank.root i).castSucc := by
            intro h
            exact hl (Fin.ext (congrArg (fun k : Fin (bank.size + 1) => k.val) h))
          simpa [c, hl, hcast] using bank.uses_bound l

def splitLeaf {n : ℕ} (bank : CopyBank n) (i : Fin n) : Fin (bank.splitRoot i).size :=
  (Fin.last bank.size).castSucc

theorem split_extension {n : ℕ} (bank : CopyBank n) (i : Fin n) :
    bank.circuit.Extends (bank.splitRoot i).circuit := .append (.append .refl _) _

theorem splitLeaf_correct {n : ℕ} (bank : CopyBank n) (i : Fin n)
    (input : Fin n → ℝ) :
    (bank.splitRoot i).circuit.evaluate input 0 (bank.splitLeaf i) = input i := by
  change ((bank.circuit.copyGate (bank.root i)).copyGate (bank.root i).castSucc).evaluate
      input 0 (Fin.last bank.size).castSucc = input i
  simp only [Circuit.copyGate_old, Circuit.copyGate_last, Pi.zero_apply, add_zero]
  exact bank.root_correct input i

theorem splitLeaf_unused {n : ℕ} (bank : CopyBank n) (i : Fin n) :
    (bank.splitRoot i).circuit.uses (bank.splitLeaf i) = 0 := by
  change ((bank.circuit.copyGate (bank.root i)).copyGate (bank.root i).castSucc).uses
      (Fin.last bank.size).castSucc = 0
  have hne : Fin.last bank.size ≠ (bank.root i).castSucc := by
    intro h
    have hv := congrArg (fun k : Fin (bank.size + 1) => k.val) h
    have hi := (bank.root i).isLt
    simp only [Fin.val_castSucc, Fin.val_last] at hv
    omega
  simp [hne]

theorem splitLeaf_not_root {n : ℕ} (bank : CopyBank n) (i j : Fin n) :
    bank.splitLeaf i ≠ (bank.splitRoot i).root j := by
  intro h
  have hv := congrArg (fun k : Fin (bank.size + 2) => k.val) h
  change bank.size = (if j = i then Fin.last (bank.size + 1)
    else (bank.root j).castSucc.castSucc).val at hv
  split_ifs at hv with hj
  · simp at hv
  · have hr := (bank.root j).isLt
    simp only [Fin.val_castSucc] at hv
    omega

theorem split_old_free {n : ℕ} (bank : CopyBank n) (i : Fin n) (k : Fin bank.size)
    (hk : ∀ j, k ≠ bank.root j) :
    (bank.splitRoot i).circuit.uses k.castSucc.castSucc = bank.circuit.uses k ∧
      ∀ j, k.castSucc.castSucc ≠ (bank.splitRoot i).root j := by
  constructor
  · have hcast : k.castSucc ≠ (bank.root i).castSucc := by
      intro h
      exact hk i (Fin.ext (congrArg (fun x : Fin (bank.size + 1) => x.val) h))
    change ((bank.circuit.copyGate (bank.root i)).copyGate (bank.root i).castSucc).uses
      k.castSucc.castSucc = _
    simp [hk i, hcast]
  · intro j h
    have hv := congrArg (fun x : Fin (bank.size + 2) => x.val) h
    change k.val = (if j = i then Fin.last (bank.size + 1)
      else (bank.root j).castSucc.castSucc).val at hv
    split_ifs at hv with hj
    · have hlt := k.isLt
      simp only [Fin.val_last] at hv
      omega
    · exact hk j (Fin.ext hv)

structure Allocation {n : ℕ} (prior : CopyBank n) (requests : List (Fin n)) where
  bank : CopyBank n
  extension : prior.circuit.Extends bank.circuit
  allocation : bank.size = prior.size + 2 * requests.length
  outputs : List (Fin bank.size)
  output_count : outputs.length = requests.length
  output_nodup : outputs.Nodup
  output_new : ∀ o ∈ outputs, prior.size ≤ o.val
  output_unused : ∀ o ∈ outputs, bank.circuit.uses o = 0
  output_free : ∀ o ∈ outputs, ∀ i, o ≠ bank.root i
  correct : ∀ input : Fin n → ℝ,
    outputs.map (bank.circuit.evaluate input 0) = requests.map input
  old_free : ∀ k : Fin prior.size, (∀ i, k ≠ prior.root i) →
    bank.circuit.uses (Fin.castLE extension.size_le k) = prior.circuit.uses k ∧
      ∀ i, Fin.castLE extension.size_le k ≠ bank.root i

def allocateStep {n : ℕ} (prior : CopyBank n) (i : Fin n) (requests : List (Fin n))
    (result : Allocation (prior.splitRoot i) requests) : Allocation prior (i :: requests) := by
  let first := Fin.castLE result.extension.size_le (prior.splitLeaf i)
  have hext := (prior.split_extension i).trans result.extension
  have hfree := result.old_free (prior.splitLeaf i) (prior.splitLeaf_not_root i)
  refine {
    bank := result.bank
    extension := hext
    allocation := ?_
    outputs := first :: result.outputs
    output_count := by simp only [List.length_cons, result.output_count]
    output_nodup := ?_
    output_new := ?_
    output_unused := ?_
    output_free := ?_
    correct := ?_
    old_free := ?_ }
  · rw [result.allocation]
    change prior.size + 2 + 2 * requests.length = prior.size + 2 * (i :: requests).length
    simp only [List.length_cons]
    omega
  · apply List.nodup_cons.mpr
    refine ⟨?_, result.output_nodup⟩
    intro hm
    have h := result.output_new first hm
    change prior.size + 2 ≤ prior.size at h
    omega
  · intro o hm
    rcases List.mem_cons.mp hm with ho | ho
    · subst o
      exact le_refl _
    · have h := result.output_new o ho
      change prior.size + 2 ≤ o.val at h
      omega
  · intro o hm
    rcases List.mem_cons.mp hm with ho | ho
    · subst o
      exact hfree.1.trans (prior.splitLeaf_unused i)
    · exact result.output_unused o ho
  · intro o hm
    rcases List.mem_cons.mp hm with ho | ho
    · subst o
      exact hfree.2
    · exact result.output_free o ho
  · intro input
    simp only [List.map_cons]
    rw [result.correct]
    have hp := result.extension.evaluate_old input (0 : Fin result.bank.size → ℝ)
      (prior.splitLeaf i)
    change result.bank.circuit.evaluate input 0 first =
      (prior.splitRoot i).circuit.evaluate input 0 (prior.splitLeaf i) at hp
    rw [hp, prior.splitLeaf_correct]
  · intro k hk
    have hs := prior.split_old_free i k hk
    have hr := result.old_free k.castSucc.castSucc hs.2
    have he : Fin.castLE hext.size_le k =
        Fin.castLE result.extension.size_le k.castSucc.castSucc := by apply Fin.ext; rfl
    rw [he]
    exact ⟨hr.1.trans hs.1, hr.2⟩

/-- Executable allocation of distinct, initially unused copy leaves for
every requested source occurrence, with exactly two equations per request. -/
def allocate {n : ℕ} (prior : CopyBank n) (requests : List (Fin n)) :
    Allocation prior requests :=
  match requests with
  | [] => {
      bank := prior
      extension := .refl
      allocation := by simp
      outputs := []
      output_count := rfl
      output_nodup := .nil
      output_new := by simp
      output_unused := by simp
      output_free := by simp
      correct := by intro input; rfl
      old_free := by intro k hk; exact ⟨rfl, hk⟩ }
  | i :: rest => allocateStep prior i rest (allocate (prior.splitRoot i) rest)

end CopyBank
end Maxwell.Logical
