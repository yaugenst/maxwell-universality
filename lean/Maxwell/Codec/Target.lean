import Maxwell.Codec.Source

/-!
# Exact target and weighted-decoder parsing

The streaming parser reconstructs all serialized physical fields and every
decoder coefficient that affects readout. Unused off-support weights are
intentionally absent. Parsed decoder rows have the same rational evaluation
as the original weighted decoder.
-/

namespace Maxwell.Codec

structure EdgeRecord where
  orientation : ℕ
  x : ℕ
  y : ℕ
  z : ℕ
  deriving DecidableEq

structure DecoderRowRecord where
  offset : ℚ
  weights : List (ℕ × ℚ)
  deriving DecidableEq

structure DecoderRecord where
  integerBits : ℕ
  fractionalBits : ℕ
  coordinates : List EdgeRecord
  rows : List DecoderRowRecord
  deriving DecidableEq

structure TargetRecord where
  outputDimension : ℕ
  nx : ℕ
  ny : ℕ
  nz : ℕ
  material : List ℚ
  source : List ℚ
  tolerance : ℚ
  decoder : DecoderRecord
  deriving DecidableEq

def edgeRecord {B : Target.Box} : B.Edge → EdgeRecord
  | .inl (i, j, k) => ⟨0, i.val, j.val, k.val⟩
  | .inr (.inl (i, j, k)) => ⟨1, i.val, j.val, k.val⟩
  | .inr (.inr (i, j, k)) => ⟨2, i.val, j.val, k.val⟩

def decoderRowRecord {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (i : Fin n) : DecoderRowRecord :=
  ⟨D.offset i, ((D.support i).sort).map fun j => (j.val, D.weight i j)⟩

def decoderRecord {B : Target.Box} {n : ℕ} (D : Target.WeightedDecoder B.Edge n) :
    DecoderRecord :=
  ⟨D.format.integerBits, D.format.fractionalBits,
    (List.ofFn D.coordinate).map edgeRecord, (List.finRange n).map (decoderRowRecord D)⟩

def targetRecord {n : ℕ} (I : Target.Instance n) : TargetRecord :=
  ⟨n, I.box.nx, I.box.ny, I.box.nz,
    (cells I.box).map I.material.value, (edges I.box).map I.source,
    I.tolerance, decoderRecord I.decoder⟩

def readEdge (bs : List Bool) : Option (EdgeRecord × List Bool) := do
  let (d, t₁) ← readNat bs
  let (x, t₂) ← readNat t₁
  let (y, t₃) ← readNat t₂
  let (z, t₄) ← readNat t₃
  pure (⟨d, x, y, z⟩, t₄)

def readWeight (bs : List Bool) : Option ((ℕ × ℚ) × List Bool) := do
  let (j, t₁) ← readNat bs
  let (q, t₂) ← readRat t₁
  pure ((j, q), t₂)

def readDecoderRow (bs : List Bool) : Option (DecoderRowRecord × List Bool) := do
  let (offset, t₁) ← readRat bs
  let (weights, t₂) ← readList readWeight t₁
  pure (⟨offset, weights⟩, t₂)

def readDecoder (bs : List Bool) : Option (DecoderRecord × List Bool) := do
  let (integerBits, t₁) ← readNat bs
  let (fractionalBits, t₂) ← readNat t₁
  let (coordinates, t₃) ← readList readEdge t₂
  let (rows, t₄) ← readList readDecoderRow t₃
  pure (⟨integerBits, fractionalBits, coordinates, rows⟩, t₄)

def readTarget (bs : List Bool) : Option (TargetRecord × List Bool) := do
  let (n, t₁) ← readNat bs
  let (nx, t₂) ← readNat t₁
  let (ny, t₃) ← readNat t₂
  let (nz, t₄) ← readNat t₃
  let (material, t₅) ← readList readRat t₄
  let (source, t₆) ← readList readRat t₅
  let (tolerance, t₇) ← readRat t₆
  let (decoder, t₈) ← readDecoder t₇
  pure (⟨n, nx, ny, nz, material, source, tolerance, decoder⟩, t₈)

theorem readEdge_append {B : Target.Box} (e : B.Edge) (tail : List Bool) :
    readEdge (edge e ++ tail) = some (edgeRecord e, tail) := by
  rcases e with (⟨i, j, k⟩ | (⟨i, j, k⟩ | ⟨i, j, k⟩)) <;>
    simp [readEdge, edge, edgeRecord, List.append_assoc, readNat_append]

theorem readWeight_append (j : ℕ) (q : ℚ) (tail : List Bool) :
    readWeight ((nat j ++ rat q) ++ tail) = some ((j, q), tail) := by
  simp [readWeight, List.append_assoc, readNat_append, readRat_append]

theorem readDecoderRow_append {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (i : Fin n) (tail : List Bool) :
    readDecoderRow ((rat (D.offset i) ++
      list (fun j : Fin D.sampleCount => nat j.val ++ rat (D.weight i j))
        ((D.support i).sort)) ++ tail) = some (decoderRowRecord D i, tail) := by
  simp [readDecoderRow, List.append_assoc, readRat_append,
    readList_map_append (fun j : Fin D.sampleCount => nat j.val ++ rat (D.weight i j))
      readWeight (fun j => (j.val, D.weight i j))
      (fun j t => readWeight_append j.val (D.weight i j) t), decoderRowRecord]

theorem readDecoder_append {B : Target.Box} {n : ℕ}
    (D : Target.WeightedDecoder B.Edge n) (tail : List Bool) :
    readDecoder (decoder D ++ tail) = some (decoderRecord D, tail) := by
  simp [readDecoder, decoder, List.append_assoc, readNat_append,
    readList_map_append edge readEdge edgeRecord readEdge_append,
    readList_map_append _ readDecoderRow (decoderRowRecord D) (readDecoderRow_append D),
    decoderRecord]

/-- Every emitted physical and decoder field has an actual streaming parser. -/
theorem readTarget_append {n : ℕ} (I : Target.Instance n) (tail : List Bool) :
    readTarget (target I ++ tail) = some (targetRecord I, tail) := by
  simp [readTarget, target, List.append_assoc, readNat_append,
    readList_map_append (fun c => rat (I.material.value c)) readRat I.material.value
      (fun c t => readRat_append (I.material.value c) t),
    readList_map_append (fun e => rat (I.source e)) readRat I.source
      (fun e t => readRat_append (I.source e) t),
    readRat_append, readDecoder_append, targetRecord]

theorem target_record_eq_of_encoding_eq {n m : ℕ} (I : Target.Instance n)
    (J : Target.Instance m) (h : target I = target J) : targetRecord I = targetRecord J := by
  have hh := congrArg (fun bs => readTarget (bs ++ [])) h
  simpa only [readTarget_append, Option.some.injEq, Prod.mk.injEq, and_true] using hh

theorem mem_triples (a b c : ℕ) (p : Fin a × Fin b × Fin c) : p ∈ triples a b c := by
  rcases p with ⟨i, j, k⟩
  simp [triples]

theorem mem_cells (B : Target.Box) (c : B.Cell) : c ∈ cells B := mem_triples _ _ _ c

theorem mem_edges (B : Target.Box) (e : B.Edge) : e ∈ edges B := by
  rcases e with (p | (p | p)) <;> simp [edges, mem_triples]

/-- The serialized cell list determines every physical scalar value. -/
theorem cell_values_injective (B : Target.Box) :
    Function.Injective (fun v : B.Cell → ℚ => (cells B).map v) := by
  intro v w h
  funext c
  exact List.map_eq_map_iff.mp h c (mem_cells B c)

/-- The serialized edge-source list determines every retained source entry. -/
theorem edge_values_injective (B : Target.Box) :
    Function.Injective (fun v : B.Edge → ℚ => (edges B).map v) := by
  intro v w h
  funext e
  exact List.map_eq_map_iff.mp h e (mem_edges B e)

theorem edgeRecord_injective (B : Target.Box) : Function.Injective (@edgeRecord B) := by
  rintro (⟨i, j, k⟩ | (⟨i, j, k⟩ | ⟨i, j, k⟩))
    (⟨i', j', k'⟩ | (⟨i', j', k'⟩ | ⟨i', j', k'⟩)) h <;>
    simp_all [edgeRecord, EdgeRecord.mk.injEq, Fin.ext_iff]

theorem decoderRecord_coordinate {B : Target.Box} {n : ℕ}
    (D : Target.WeightedDecoder B.Edge n) (j : Fin D.sampleCount) :
    (decoderRecord D).coordinates[j.val]'(by simp [decoderRecord]) =
      edgeRecord (D.coordinate j) := by simp [decoderRecord]

theorem decoderRecord_row {B : Target.Box} {n : ℕ}
    (D : Target.WeightedDecoder B.Edge n) (i : Fin n) :
    (decoderRecord D).rows[i.val]'(by simp [decoderRecord]) = decoderRowRecord D i := by
  simp [decoderRecord]

/-- A parsed supported pair records the precise support and actual weight. -/
theorem decoderRowRecord_weight_iff {ι : Type*} {n : ℕ}
    (D : Target.WeightedDecoder ι n) (i : Fin n) (j : Fin D.sampleCount) (q : ℚ) :
    (j.val, q) ∈ (decoderRowRecord D i).weights ↔ j ∈ D.support i ∧ D.weight i j = q := by
  simp only [decoderRowRecord, List.mem_map, Finset.mem_sort, Prod.mk.injEq]
  constructor
  · rintro ⟨k, hk, hkj, hq⟩
    have h : k = j := Fin.ext hkj
    subst k
    exact ⟨hk, hq⟩
  · rintro ⟨hj, hq⟩
    exact ⟨j, hj, rfl, hq⟩

def DecoderRowRecord.evaluate (row : DecoderRowRecord) (samples : ℕ → ℚ) : ℚ :=
  row.offset + (row.weights.map fun p => p.2 * samples p.1).sum

theorem decoderRowRecord_evaluate {ι : Type*} {n : ℕ}
    (D : Target.WeightedDecoder ι n) (i : Fin n) (samples : ℕ → ℚ) :
    (decoderRowRecord D i).evaluate samples =
      D.offset i + ∑ j ∈ D.support i, D.weight i j * samples j.val := by
  simp only [DecoderRowRecord.evaluate, decoderRowRecord, List.map_map, Function.comp_def]
  congr 1
  simpa only [Finset.sort_toFinset] using
    (List.sum_toFinset (fun j : Fin D.sampleCount => D.weight i j * samples j.val)
      ((D.support i).sort_nodup (· ≤ ·))).symm

/-- The parsed row evaluates to the original decoder on every finite
message whose sampled rational values are supplied. -/
theorem decoderRowRecord_decode {ι : Type*} {n : ℕ}
    (D : Target.WeightedDecoder ι n) (w : D.Messages) (i : Fin n)
    (samples : ℕ → ℚ) (hs : ∀ j : Fin D.sampleCount, samples j.val = D.format.value (w j)) :
    (decoderRowRecord D i).evaluate samples = D.decode w i := by
  simp [decoderRowRecord_evaluate, hs, Target.WeightedDecoder.decode]

/-- Parsed target equality preserves the actual physical geometry, matrix,
source, and tolerance. Heterogeneous equality accounts only for the dependent
finite index types attached to the reconstructed box. -/
theorem targetRecord_physical_faithful {n m : ℕ} (I : Target.Instance n)
    (J : Target.Instance m) (h : targetRecord I = targetRecord J) :
    I.box = J.box ∧ HEq (Target.maxwell I.material) (Target.maxwell J.material) ∧
      HEq I.source J.source ∧ I.tolerance = J.tolerance := by
  rcases I with ⟨B, material, source, tolerance, tolerance_pos, decoder⟩
  rcases J with ⟨B', material', source', tolerance', tolerance_pos', decoder'⟩
  have hB : B = B' := by
    have hx := congrArg TargetRecord.nx h
    have hy := congrArg TargetRecord.ny h
    have hz := congrArg TargetRecord.nz h
    change B.nx = B'.nx at hx
    change B.ny = B'.ny at hy
    change B.nz = B'.nz at hz
    cases B
    cases B'
    simp_all
  subst B'
  have hmaterial := congrArg TargetRecord.material h
  have hsource := congrArg TargetRecord.source h
  have htolerance := congrArg TargetRecord.tolerance h
  change (cells B).map material.value = (cells B).map material'.value at hmaterial
  change (edges B).map source = (edges B).map source' at hsource
  have hm := cell_values_injective B hmaterial
  have hs := edge_values_injective B hsource
  have hmatrix : Target.maxwell material = Target.maxwell material' :=
    congrArg (Target.operator B) hm
  exact ⟨rfl, heq_of_eq hmatrix, heq_of_eq hs, htolerance⟩

end Maxwell.Codec
