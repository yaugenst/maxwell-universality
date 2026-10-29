import Maxwell.Target
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Finset.Sort

/-!
# Explicit Boolean input, target, access, and output representations

Natural numbers use a unary binary-length header followed by little-endian
binary digits. Signed integers add a sign bit, and rationals store their
canonical numerator and positive denominator. Lists carry an element count.

Sparse input encoding visits only the stored matrix support. Target material
and sources use explicit nested coordinate loops. A decoder emits its selected
coordinates, support sets, supported rational weights, and rational offsets;
its unused weights outside support have no observable meaning and are omitted.
This module does not claim a bit-machine running-time bound for these Lean
definitions. Such bounds must be proved for the actual machine implementation.
-/

namespace Maxwell.Codec

/-- Little-endian binary evaluation. -/
def bitsValue : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * bitsValue bs

/-- Self-delimiting natural-number representation, including zero. -/
def nat (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ false :: n.bits

/-- The sign bit is true exactly for negative integers. -/
def int (z : ℤ) : List Bool := decide (z < 0) :: nat z.natAbs

def rat (q : ℚ) : List Bool := int q.num ++ nat q.den

/-- Count-prefixed concatenation; the element codec supplies its own framing. -/
def list {α : Type*} (encode : α → List Bool) (xs : List α) : List Bool :=
  nat xs.length ++ xs.flatMap encode

def vector {n : ℕ} (x : Fin n → ℚ) : List Bool := list rat (List.ofFn x)

/-- Explicit lexicographic nested loops, with no enumeration oracle. -/
def triples (a b c : ℕ) : List (Fin a × Fin b × Fin c) :=
  (List.finRange a).flatMap fun i =>
    (List.finRange b).flatMap fun j => (List.finRange c).map fun k => (i, j, k)

def cells (B : Target.Box) : List B.Cell := triples B.nx B.ny B.nz

def edges (B : Target.Box) : List B.Edge :=
  (triples B.nx (B.ny - 1) (B.nz - 1)).map Sum.inl ++
  (triples (B.nx - 1) B.ny (B.nz - 1)).map (Sum.inr ∘ Sum.inl) ++
  (triples (B.nx - 1) (B.ny - 1) B.nz).map (Sum.inr ∘ Sum.inr)

/-- Orientation tag followed by the three stored, bounded coordinate indices. -/
def edge {B : Target.Box} : B.Edge → List Bool
  | .inl (i, j, k) => nat 0 ++ nat i.val ++ nat j.val ++ nat k.val
  | .inr (.inl (i, j, k)) => nat 1 ++ nat i.val ++ nat j.val ++ nat k.val
  | .inr (.inr (i, j, k)) => nat 2 ++ nat i.val ++ nat j.val ++ nat k.val

private def pairKey {n : ℕ} (p : Fin n × Fin n) : ℕ := n * p.1.val + p.2.val

private theorem pairKey_injective (n : ℕ) : Function.Injective (@pairKey n) := by
  intro p q h
  have hn : 0 < n := Nat.zero_lt_of_lt p.1.isLt
  have hc := congrArg (fun k => k % n) h
  have hr := congrArg (fun k => k / n) h
  simp only [pairKey, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add,
    Nat.mod_eq_of_lt p.2.isLt, Nat.mod_eq_of_lt q.2.isLt] at hc
  simp only [pairKey, Nat.mul_add_div hn, Nat.div_eq_of_lt p.2.isLt,
    Nat.div_eq_of_lt q.2.isLt, Nat.add_zero] at hr
  exact Prod.ext (Fin.ext hr) (Fin.ext hc)

private def pairLE {n : ℕ} (p q : Fin n × Fin n) : Prop := pairKey p ≤ pairKey q

private instance {n : ℕ} : DecidableRel (@pairLE n) := fun _ _ => inferInstanceAs (Decidable (_ ≤ _))
private instance {n : ℕ} : IsTrans (Fin n × Fin n) pairLE :=
  ⟨fun _ _ _ hab hbc => le_trans hab hbc⟩
private instance {n : ℕ} : Std.Total (@pairLE n) :=
  ⟨fun a b => le_total (pairKey a) (pairKey b)⟩
private instance {n : ℕ} : Std.Antisymm (@pairLE n) :=
  ⟨fun _ _ hab hba => pairKey_injective n (le_antisymm hab hba)⟩

/-- Canonical row-major order on the already stored support; no dense `n²` scan. -/
def sourceEntries (S : Source.SparseSystem) : List (Fin S.n × Fin S.n) :=
  S.matrix.support.sort pairLE

/-- The canonical sparse stream visits each row in one contiguous block. -/
theorem sourceEntries_rows_sorted (S : Source.SparseSystem) :
    (sourceEntries S).Pairwise (fun p q => p.1.val ≤ q.1.val) := by
  apply (S.matrix.support.pairwise_sort pairLE).imp
  intro p q h
  change S.n * p.1.val + p.2.val ≤ S.n * q.1.val + q.2.val at h
  have hn : 0 < S.n := Nat.zero_lt_of_lt p.1.isLt
  have hc := q.2.isLt
  by_contra hrow
  have hrow' : q.1.val + 1 ≤ p.1.val := by omega
  have hm := Nat.mul_le_mul_left S.n hrow'
  nlinarith

theorem mem_sourceEntries (S : Source.SparseSystem) (p : Fin S.n × Fin S.n) :
    p ∈ sourceEntries S ↔ p ∈ S.matrix.support := by
  simp [sourceEntries]

theorem sourceEntries_length (S : Source.SparseSystem) :
    (sourceEntries S).length = S.nnz := by
  simp [sourceEntries, Source.SparseSystem.nnz, SparseRationalMatrix.nnz]

/-- A stored coefficient is read directly through its support proof. The
proof is erased; this definition does not search the support for its value. -/
def sourceEntry (S : Source.SparseSystem)
    (p : {p // p ∈ sourceEntries S}) : List Bool :=
  nat p.val.1.val ++ nat p.val.2.val ++
    rat (S.matrix.coefficient ⟨p.val, (mem_sourceEntries S p.val).mp p.property⟩)

def source (S : Source.SparseSystem) : List Bool :=
  nat S.n ++ list (sourceEntry S) (sourceEntries S).attach ++ vector S.source

def decoder {B : Target.Box} {n : ℕ} (D : Target.WeightedDecoder B.Edge n) : List Bool :=
  nat D.format.integerBits ++ nat D.format.fractionalBits ++
    list edge (List.ofFn D.coordinate) ++
    list (fun i : Fin n =>
      rat (D.offset i) ++
        list (fun j : Fin D.sampleCount => nat j.val ++ rat (D.weight i j))
          ((D.support i).sort)) (List.finRange n)

/-- Complete physical data and every coefficient used by the finite decoder. -/
def target {n : ℕ} (I : Target.Instance n) : List Bool :=
  nat n ++ nat I.box.nx ++ nat I.box.ny ++ nat I.box.nz ++
    list (fun c => rat (I.material.value c)) (cells I.box) ++
    list (fun e => rat (I.source e)) (edges I.box) ++
    rat I.tolerance ++ decoder I.decoder

/-- A fixed-width access word has exactly the prescribed number of bits. -/
def word (F : Target.FixedPointFormat) (w : F.Word) : List Bool :=
  List.ofFn fun i : Fin F.width => w.val.testBit i.val

/-- Raw access messages have no redundant per-word framing: their count and
word width are already in the emitted decoder. -/
def messages {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (w : D.Messages) : List Bool :=
  (List.ofFn w).flatMap (word D.format)

def output {n : ℕ} (x : Fin n → ℚ) : List Bool := vector x

theorem word_length (F : Target.FixedPointFormat) (w : F.Word) :
    (word F w).length = F.width := by simp [word]

theorem messages_length {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (w : D.Messages) : (messages D w).length = D.sampleCount * D.format.width := by
  simp [messages, List.length_flatMap, word, Function.comp_def]

/-- Parse the unary length header, returning the unconsumed bits. -/
def readLength : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: bs => some (0, bs)
  | true :: bs => do
      let (n, rest) ← readLength bs
      pure (n + 1, rest)

def readNat (bs : List Bool) : Option (ℕ × List Bool) := do
  let (n, rest) ← readLength bs
  if n ≤ rest.length then
    pure (bitsValue (rest.take n), rest.drop n)
  else none

def readInt : List Bool → Option (ℤ × List Bool)
  | [] => none
  | sign :: bs => do
      let (n, rest) ← readNat bs
      pure (if sign then -(n : ℤ) else (n : ℤ), rest)

def readRat (bs : List Bool) : Option (ℚ × List Bool) := do
  let (z, tail) ← readInt bs
  let (d, rest) ← readNat tail
  if d = 0 then none else pure ((z : ℚ) / (d : ℚ), rest)

theorem bitsValue_bits (n : ℕ) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitsValue]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b with
    | false => simp [bitsValue, ih, Nat.bit]
    | true => simp [bitsValue, ih, Nat.bit]; omega

theorem readLength_prefix (n : ℕ) (tail : List Bool) :
    readLength (List.replicate n true ++ false :: tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, readLength, ih]

/-- Parsing a natural consumes exactly its own self-delimiting word. -/
theorem readNat_append (n : ℕ) (tail : List Bool) :
    readNat (nat n ++ tail) = some (n, tail) := by
  simp [readNat, nat, List.append_assoc, readLength_prefix, bitsValue_bits]

theorem nat_injective : Function.Injective nat := by
  intro a b h
  have hh := congrArg (fun bs => readNat (bs ++ [])) h
  simpa only [readNat_append, Option.some.injEq, Prod.mk.injEq, and_true] using hh

theorem readInt_append (z : ℤ) (tail : List Bool) :
    readInt (int z ++ tail) = some (z, tail) := by
  simp only [int, List.cons_append, readInt, readNat_append]
  by_cases h : z < 0
  · simp [h, abs_of_neg h]
  · simp [h, abs_of_nonneg (le_of_not_gt h)]

theorem int_injective : Function.Injective int := by
  intro a b h
  have hh := congrArg (fun bs => readInt (bs ++ [])) h
  simpa only [readInt_append, Option.some.injEq, Prod.mk.injEq, and_true] using hh

theorem readRat_append (q : ℚ) (tail : List Bool) :
    readRat (rat q ++ tail) = some (q, tail) := by
  simp [rat, readRat, List.append_assoc, readInt_append, readNat_append,
    q.den_ne_zero, q.num_div_den]

theorem rat_injective : Function.Injective rat := by
  intro a b h
  have hh := congrArg (fun bs => readRat (bs ++ [])) h
  simpa only [readRat_append, Option.some.injEq, Prod.mk.injEq, and_true] using hh

/-- Bounded-count parser used by every length-prefixed list. -/
def readMany {α : Type*} (parse : List Bool → Option (α × List Bool)) :
    ℕ → List Bool → Option (List α × List Bool)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
      let (x, tail) ← parse bs
      let (xs, rest) ← readMany parse n tail
      pure (x :: xs, rest)

def readList {α : Type*} (parse : List Bool → Option (α × List Bool))
    (bs : List Bool) : Option (List α × List Bool) :=
  match readNat bs with
  | none => none
  | some (n, tail) => readMany parse n tail

theorem readMany_append {α : Type*} (encode : α → List Bool)
    (parse : List Bool → Option (α × List Bool))
    (hparse : ∀ x tail, parse (encode x ++ tail) = some (x, tail))
    (xs : List α) (tail : List Bool) :
    readMany parse xs.length (xs.flatMap encode ++ tail) = some (xs, tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [readMany, List.append_assoc, hparse, ih]

/-- The list parser preserves the entire unconsumed suffix. -/
theorem readList_append {α : Type*} (encode : α → List Bool)
    (parse : List Bool → Option (α × List Bool))
    (hparse : ∀ x tail, parse (encode x ++ tail) = some (x, tail))
    (xs : List α) (tail : List Bool) :
    readList parse (list encode xs ++ tail) = some (xs, tail) := by
  simp [readList, list, List.append_assoc, readNat_append,
    readMany_append encode parse hparse]

theorem list_injective {α : Type*} (encode : α → List Bool)
    (parse : List Bool → Option (α × List Bool))
    (hparse : ∀ x tail, parse (encode x ++ tail) = some (x, tail)) :
    Function.Injective (list encode) := by
  intro xs ys h
  have hh := congrArg (fun bs => readList parse (bs ++ [])) h
  simpa only [readList_append encode parse hparse, Option.some.injEq,
    Prod.mk.injEq, and_true] using hh

theorem output_injective (n : ℕ) : Function.Injective (@output n) := by
  intro x y h
  apply List.ofFn_injective
  exact list_injective rat readRat readRat_append h

end Maxwell.Codec
