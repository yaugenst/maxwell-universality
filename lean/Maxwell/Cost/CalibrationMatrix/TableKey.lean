import Maxwell.Green.CalibrationTable
import Maxwell.Cost.FixedWidth
import Maxwell.Cost.Counter

/-! An explicit 34-bit key for the fixed stencil decision table. -/
namespace Maxwell.Cost.CalibrationMatrix.TableKey
open Maxwell.Defect.FiniteStencil Maxwell.Spectral.Lattice

def field (width n : ℕ) : List Bool := FixedWidth.bits width n.bits

def encode (key : StencilKey) : List Bool :=
  field 2 key.edge.1.val ++
  (field 5 (key.edge.2 0).val ++
  (field 5 (key.edge.2 1).val ++
  (field 5 (key.edge.2 2).val ++
  (List.ofFn key.hit ++ [key.diagonal]))))

def decode (bits : List Bool) : StencilKey where
  edge := (Fin.ofNat 3 (addressValue (bits.take 2)),
    ![(addressValue ((bits.drop 2).take 5) : ZMod 20),
      (addressValue ((bits.drop 7).take 5) : ZMod 20),
      (addressValue ((bits.drop 12).take 5) : ZMod 20)])
  hit k := ((bits.drop 17)[k.val]?).getD false
  diagonal := (bits.drop 33).head?.getD false

@[simp] theorem field_length (width n : ℕ) : (field width n).length = width :=
  FixedWidth.bits_length width n.bits

theorem field_value (width n : ℕ) (h : n.size ≤ width) : addressValue (field width n) = n := by
  rw [field, FixedWidth.bits_value _ _ (by simpa only [Nat.size_eq_bits_len] using h), addressValue_bits]

@[simp] theorem encode_length (key : StencilKey) : (encode key).length = 34 := by
  simp only [encode, List.length_append, field_length, List.length_ofFn, List.length_singleton]

private theorem field_prefix (width n : ℕ) (rest : List Bool) :
    (field width n ++ rest).take width = field width n := by
  simpa only [field_length] using (show (field width n ++ rest).take (field width n).length = field width n from List.take_left)

private theorem field_suffix (width n : ℕ) (rest : List Bool) :
    (field width n ++ rest).drop width = rest := by
  simpa only [field_length] using (show (field width n ++ rest).drop (field width n).length = rest from List.drop_left)

private theorem direction_size (d : Fin 3) : d.val.size ≤ 2 := by
  fin_cases d <;> decide

private theorem coordinate_size (x : ZMod 20) : x.val.size ≤ 5 := by
  apply (Nat.size_le).mpr
  have h := ZMod.val_lt x
  norm_num
  omega

/-- Explicit byte-free serialization round trip; the static table consumes
only two direction bits, fifteen residue bits and seventeen test bits. -/
theorem decode_encode (key : StencilKey) : decode (encode key) = key := by
  have h2 : (encode key).drop 2 = field 5 (key.edge.2 0).val ++
      (field 5 (key.edge.2 1).val ++
      (field 5 (key.edge.2 2).val ++ (List.ofFn key.hit ++ [key.diagonal]))) :=
    field_suffix _ _ _
  have h7 : (encode key).drop 7 = field 5 (key.edge.2 1).val ++
      (field 5 (key.edge.2 2).val ++ (List.ofFn key.hit ++ [key.diagonal])) := by
    rw [show (7 : ℕ) = 2 + 5 from rfl, ← List.drop_drop, h2, field_suffix]
  have h12 : (encode key).drop 12 = field 5 (key.edge.2 2).val ++
      (List.ofFn key.hit ++ [key.diagonal]) := by
    rw [show (12 : ℕ) = 7 + 5 from rfl, ← List.drop_drop, h7, field_suffix]
  have h17 : (encode key).drop 17 = List.ofFn key.hit ++ [key.diagonal] := by
    rw [show (17 : ℕ) = 12 + 5 from rfl, ← List.drop_drop, h12, field_suffix]
  have h33 : (encode key).drop 33 = [key.diagonal] := by
    rw [show (33 : ℕ) = 17 + 16 from rfl, ← List.drop_drop, h17]
    simpa only [List.length_ofFn] using (show (List.ofFn key.hit ++ [key.diagonal]).drop (List.ofFn key.hit).length = [key.diagonal] from List.drop_left)
  apply StencilKey.ext
  · apply Prod.ext
    · apply Fin.ext
      simp only [decode, encode, field_prefix, field_value 2 _ (direction_size _), Fin.val_ofNat]
      exact Nat.mod_eq_of_lt key.edge.1.isLt
    · funext j
      fin_cases j <;>
        simp only [decode, h2, h7, h12, field_prefix,
          field_value 5 _ (coordinate_size _), ZMod.natCast_zmod_val] <;> rfl
  · funext k
    have hk : k.val < (List.ofFn key.hit).length := by simpa only [List.length_ofFn] using k.isLt
    simp only [decode, h17]
    rw [List.getElem?_append_left hk]
    simp only [List.getElem?_ofFn, k.isLt, dite_true, Option.getD_some]
  · simp only [decode, h33, List.head?_cons, Option.getD_some]

end Maxwell.Cost.CalibrationMatrix.TableKey
