import Maxwell.Codec.Bounds

/-! Exact rational outputs need not be reduced. The actual emitted numerator
and denominator, including their actual serialized lengths, are bounded here.
This avoids demanding a greatest-common-divisor computation from the decoder.
The interpretation is fixed and independent of the source problem. -/

namespace Maxwell.Codec

structure RationalPair where
  numerator : ℤ
  denominator : ℕ
  denominator_pos : 0 < denominator
  deriving DecidableEq

namespace RationalPair

def value (q : RationalPair) : ℚ := (q.numerator : ℚ) / q.denominator

def encode (q : RationalPair) : List Bool := int q.numerator ++ nat q.denominator

def Short (B : ℕ) (q : RationalPair) : Prop :=
  signedBitLength q.numerator ≤ B ∧ unsignedBitLength q.denominator ≤ B

def canonical (q : ℚ) : RationalPair := ⟨q.num, q.den, q.den_pos⟩

@[simp] theorem canonical_value (q : ℚ) : (canonical q).value = q := q.num_div_den

@[simp] theorem canonical_encode (q : ℚ) : (canonical q).encode = rat q := rfl

theorem canonical_short {B : ℕ} {q : ℚ} (h : Source.ShortRational B q) :
    (canonical q).Short B := by
  constructor
  · change signedBitLength q.num ≤ B
    exact_mod_cast h.1
  · change unsignedBitLength q.den ≤ B
    exact_mod_cast h.2

theorem encode_length (q : RationalPair) :
    q.encode.length = 2 *
      (signedBitLength q.numerator + unsignedBitLength q.denominator) + 1 := by
  simp [encode, int_length, nat_length]
  omega

theorem encode_length_le {B : ℕ} {q : RationalPair} (h : q.Short B) :
    q.encode.length ≤ 4 * B + 1 := by
  rw [encode_length]
  rcases h with ⟨hn, hd⟩
  omega

/-- The fixed parser checks positivity before assigning rational semantics. -/
def read (bs : List Bool) : Option (RationalPair × List Bool) := do
  let (z, tail) ← readInt bs
  let (d, rest) ← readNat tail
  if h : 0 < d then pure (⟨z, d, h⟩, rest) else none

theorem read_append (q : RationalPair) (tail : List Bool) :
    read (q.encode ++ tail) = some (q, tail) := by
  simp [read, encode, List.append_assoc, readInt_append, readNat_append,
    q.denominator_pos]

end RationalPair

/-- A fully specified raw representation of a rational output vector. Every
integer uses the self-delimiting canonical integer codec even when a rational
pair is unreduced. Thus padded headers cannot evade the bit bound. -/
def RepresentsOutput {n : ℕ} (B : ℕ) (x : Fin n → ℚ) (bits : List Bool) : Prop :=
  ∃ pairs : Fin n → RationalPair,
    bits = list RationalPair.encode (List.ofFn pairs) ∧
    (∀ i, (pairs i).value = x i) ∧ ∀ i, (pairs i).Short B

theorem canonical_represents {n B : ℕ} (x : Fin n → ℚ)
    (hx : ∀ i, Source.ShortRational B (x i)) :
    RepresentsOutput B x (output x) := by
  refine ⟨fun i => RationalPair.canonical (x i), ?_, ?_, ?_⟩
  · simp only [output, vector, list, List.length_ofFn]
    congr 1
    rw [show (List.ofFn fun i => RationalPair.canonical (x i)) =
      (List.ofFn x).map RationalPair.canonical by rw [List.map_ofFn]; rfl,
      List.flatMap_map]
    rfl
  · intro i; exact RationalPair.canonical_value (x i)
  · intro i; exact RationalPair.canonical_short (hx i)

/-- Every admitted output is parsed completely to exactly the stated values. -/
theorem represents_output_parses {n B : ℕ} (x : Fin n → ℚ) (bits : List Bool)
    (h : RepresentsOutput B x bits) :
    (readList RationalPair.read bits).map (fun result =>
      (result.1.map RationalPair.value, result.2)) = some (List.ofFn x, []) := by
  obtain ⟨pairs, rfl, hvalue, _⟩ := h
  have hh := readList_append RationalPair.encode RationalPair.read
    RationalPair.read_append (List.ofFn pairs) []
  simp only [List.append_nil] at hh
  rw [hh]
  simp only [Option.map_some]
  congr 2
  simp [List.map_ofFn, Function.comp_def, hvalue]

/-- The raw representation size follows from the same literal word bound,
without relying on cancellation in a normalized rational number. -/
theorem represents_output_length {n B : ℕ} (x : Fin n → ℚ) (bits : List Bool)
    (h : RepresentsOutput B x bits) :
    bits.length ≤ 2 * unsignedBitLength n + 1 + n * (4 * B + 1) := by
  obtain ⟨pairs, rfl, _, hshort⟩ := h
  have hh := list_length_le RationalPair.encode (List.ofFn pairs) (4 * B + 1)
    (fun q hq => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
      exact RationalPair.encode_length_le (hshort i))
  simpa using hh

end Maxwell.Codec
