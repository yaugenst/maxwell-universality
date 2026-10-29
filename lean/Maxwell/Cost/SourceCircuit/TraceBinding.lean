import Maxwell.Cost.SourceCircuit.AllocationScan
import Maxwell.Cost.SourceCircuit.Roots
import Maxwell.Cost.SourceCircuit.EmitGate
import Maxwell.Cost.FixedWidth

/-! The retained bytes of the finite allocator represent the chronological
copy gates and exposed leaves of the logical copy bank. -/

namespace Maxwell.Cost.SourceCircuit

def fixedWidth (width id : ℕ) : List Bool := FixedWidth.bits width id.bits

@[simp] theorem fixedWidth_length (width id : ℕ) :
    (fixedWidth width id).length = width := FixedWidth.bits_length _ _

theorem addressValue_injective_of_length {xs ys : List Bool}
    (hlen : xs.length = ys.length) (hvalue : addressValue xs = addressValue ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => simpa using hlen.symm
  | cons b xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons c ys =>
      have ht : xs.length = ys.length := by simpa using hlen
      cases b <;> cases c <;> simp only [addressValue, Bool.toNat_false,
        Bool.toNat_true] at hvalue
      · exact congrArg (List.cons false) (ih ht (by omega))
      · omega
      · omega
      · exact congrArg (List.cons true) (ih ht (by omega))

theorem fixedWidth_value (width id : ℕ) (h : id < 2 ^ width) :
    addressValue (fixedWidth width id) = id := by
  rw [fixedWidth, FixedWidth.bits_value, addressValue_bits]
  rwa [Nat.size_eq_bits_len, Nat.size_le]

theorem fixedWidth_eq {width id : ℕ} {word : List Bool}
    (hlen : word.length = width) (hvalue : addressValue word = id) :
    word = fixedWidth width id := by
  apply addressValue_injective_of_length (hlen.trans (fixedWidth_length _ _).symm)
  rw [fixedWidth_value _ _ (by
    rw [← hvalue, ← hlen]
    exact IndexedAddress.value_lt_pow_length word), hvalue]

/-- Only the five gate types emitted by the dyadic compiler have tags. -/
def gateBytes (width : ℕ) : Logical.GateRecord → Option (List Bool)
  | .zero => some zeroTag
  | .scale parent weight =>
      if weight = 1 then some (copyTag ++ fixedWidth width parent)
      else if weight = 1 / 2 then some (halfTag ++ fixedWidth width parent)
      else if weight = -1 then some (negativeTag ++ fixedWidth width parent)
      else none
  | .add left right => some (additionTag ++ fixedWidth width left ++ fixedWidth width right)

def traceBytes (width : ℕ) : List Logical.GateRecord → Option (List Bool)
  | [] => some []
  | gate :: rest => do
      let head ← gateBytes width gate
      let tail ← traceBytes width rest
      pure (head ++ tail)

theorem traceBytes_append (width : ℕ) (a b : List Logical.GateRecord)
    {xs ys : List Bool} (ha : traceBytes width a = some xs)
    (hb : traceBytes width b = some ys) :
    traceBytes width (a ++ b) = some (xs ++ ys) := by
  induction a generalizing xs with
  | nil =>
    have hx : xs = [] := by simpa [traceBytes] using ha.symm
    simpa [hx] using hb
  | cons g a ih =>
    cases hg : gateBytes width g with
    | none => simp [traceBytes, hg] at ha
    | some head =>
      cases ht : traceBytes width a with
      | none => simp [traceBytes, hg, ht] at ha
      | some tail =>
        have hx : head ++ tail = xs := by simpa [traceBytes, hg, ht] using ha
        rw [← hx]
        simp [traceBytes, hg, ih ht, List.append_assoc]

def copyArchive {n : ℕ} (width : ℕ) (bank : Logical.CopyBank n) :
    List (Fin n) → List Bool
  | [] => []
  | i :: rest => copyTag ++ fixedWidth width (bank.root i).val ++
      copyTag ++ fixedWidth width (bank.root i).val ++
      copyArchive width (bank.splitRoot i) rest

theorem copyArchive_trace {n : ℕ} (width : ℕ) (bank : Logical.CopyBank n)
    (requests : List (Fin n)) :
    traceBytes width (bank.trace requests) = some (copyArchive width bank requests) := by
  induction requests generalizing bank with
  | nil => rfl
  | cons i rest ih =>
    simp [Logical.CopyBank.trace, traceBytes, gateBytes, copyArchive, ih, List.append_assoc]

def copyLeaves {n : ℕ} (bank : Logical.CopyBank n) : List (Fin n) → List ℕ
  | [] => []
  | i :: rest => bank.size :: copyLeaves (bank.splitRoot i) rest

theorem copyLeaves_outputs {n : ℕ} (bank : Logical.CopyBank n)
    (requests : List (Fin n)) :
    copyLeaves bank requests = (bank.allocate requests).outputs.map Fin.val := by
  induction requests generalizing bank with
  | nil => rfl
  | cons i rest ih =>
    change bank.size :: copyLeaves (bank.splitRoot i) rest =
      bank.size :: ((bank.splitRoot i).allocate rest).outputs.map Fin.val
    exact congrArg (List.cons bank.size) (ih (bank.splitRoot i))

structure AllocationData.Matches {n : ℕ} (width : ℕ)
    (bank : Logical.CopyBank n) (d : AllocationData n) : Prop where
  roots : RepresentsRoots bank d.roots
  rootLength : ∀ i, (d.roots.get i).length = width
  next : addressValue d.next = bank.size
  nextLength : d.next.length = width

theorem AllocationData.Matches.split {n : ℕ} {width : ℕ}
    {bank : Logical.CopyBank n} {d : AllocationData n}
    (h : d.Matches width bank) (base : ℕ) (i : Fin n)
    (room : bank.size + 2 < 2 ^ width) :
    (d.split base width i).Matches width (bank.splitRoot i) := by
  have first : (Increment.bits d.next).length = width := by
    rw [increment_length d.next (by rw [h.next, h.nextLength]; omega), h.nextLength]
  refine ⟨representsRoots_split bank d.roots i d.next h.roots h.next, ?_,
    split_next_value bank i d.next h.next, ?_⟩
  · intro j
    change ((d.roots.set i (Increment.bits d.next)).get j).length = width
    have hset : (d.roots.set i (Increment.bits d.next)).get j =
        if i = j then Increment.bits d.next else d.roots.get j := by
      simp [Vector.get, Fin.cast, Array.getElem_set, Fin.ext_iff]
    rw [hset]
    split_ifs
    · exact first
    · exact h.rootLength j
  · change (Increment.bits (Increment.bits d.next)).length = width
    rw [increment_length (Increment.bits d.next) (by
      rw [Increment.bits_value, h.next, first]; omega), first]

def allocationFold {n : ℕ} (base width : ℕ) :
    List (Fin n) → AllocationData n → AllocationData n
  | [], d => d
  | i :: rest, d => allocationFold base width rest (d.split base width i)

theorem allocationFold_binding {n : ℕ} (base width : ℕ)
    (bank : Logical.CopyBank n) (requests : List (Fin n)) (d : AllocationData n)
    (hm : d.Matches width bank) (room : bank.size + 2 * requests.length < 2 ^ width) :
    (allocationFold base width requests d).Matches width (bank.allocate requests).bank ∧
      (allocationFold base width requests d).gates = d.gates ++ copyArchive width bank requests ∧
      (allocationFold base width requests d).leaves = d.leaves ++
        (copyLeaves bank requests).flatMap (fixedWidth width) := by
  induction requests generalizing bank d with
  | nil => simp [allocationFold, copyArchive, copyLeaves, Logical.CopyBank.allocate, hm]
  | cons i rest ih =>
    have short : bank.size + 2 < 2 ^ width := by
      simp only [List.length_cons] at room
      omega
    have remain : (bank.splitRoot i).size + 2 * rest.length < 2 ^ width := by
      change bank.size + 2 + 2 * rest.length < _
      simp only [List.length_cons] at room
      omega
    obtain ⟨matched, gates, leaves⟩ := ih (bank.splitRoot i) (d.split base width i)
      (hm.split base i short) remain
    have root : d.roots.get i = fixedWidth width (bank.root i).val :=
      fixedWidth_eq (hm.rootLength i) (hm.roots i)
    have next : d.next = fixedWidth width bank.size := fixedWidth_eq hm.nextLength hm.next
    refine ⟨matched, ?_, ?_⟩
    · simpa [allocationFold, AllocationData.split, copyArchive, root, List.append_assoc] using gates
    · simpa [allocationFold, AllocationData.split, copyLeaves, next, List.append_assoc] using leaves

theorem scanBits_fold_allocation {n : ℕ} (base width : ℕ) (i : Fin n)
    (bits : List Bool) (d : AllocationData n) :
    ScanBits.fold (AllocationData.split base width i) bits d =
      allocationFold base width (List.replicate (bits.count true) i) d := by
  induction bits generalizing d with
  | nil => rfl
  | cons b bits ih =>
    cases b <;> simp [ScanBits.fold, List.replicate_succ, allocationFold, ih]

theorem allocationScan_binding {n : ℕ} (base width : ℕ)
    (bank : Logical.CopyBank n) (i : Fin n) (bits : List Bool) (d : AllocationData n)
    (hm : d.Matches width bank) (room : bank.size + 2 * bits.count true < 2 ^ width) :
    let requests := List.replicate (bits.count true) i
    let result := ScanBits.fold (AllocationData.split base width i) bits d
    result.Matches width (bank.allocate requests).bank ∧
      traceBytes width (bank.trace requests) =
        some (copyArchive width bank requests) ∧
      result.gates = d.gates ++ copyArchive width bank requests ∧
      result.leaves = d.leaves ++
        ((bank.allocate requests).outputs.map Fin.val).flatMap (fixedWidth width) := by
  dsimp only
  rw [scanBits_fold_allocation]
  obtain ⟨matched, gates, leaves⟩ := allocationFold_binding base width bank
    (List.replicate (bits.count true) i) d hm (by simpa using room)
  exact ⟨matched, copyArchive_trace width bank _, gates,
    by simpa [copyLeaves_outputs] using leaves⟩

end Maxwell.Cost.SourceCircuit
