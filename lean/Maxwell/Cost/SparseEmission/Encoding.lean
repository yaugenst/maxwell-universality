import Maxwell.Cost.SourceCircuit.TraceBinding

namespace Maxwell.Cost.SparseEmission

/-- The sparse matrix alphabet uses a sign bit and a half-magnitude bit. -/
def flagValue (negative half : Bool) : ℚ :=
  (if negative then -1 else 1) / (if half then 2 else 1)

def valueBits (value : ℚ) : List Bool :=
  [decide (value < 0), decide (value = 1/2 ∨ value = -1/2)]

theorem valueBits_flags (negative half : Bool) :
    valueBits (flagValue negative half) = [negative,half] := by
  cases negative <;> cases half <;> norm_num [valueBits,flagValue]

def entryWire (width : ℕ) (entry : Logical.RationalCode.Entry) : List Bool :=
  SourceCircuit.fixedWidth width entry.row ++ SourceCircuit.fixedWidth width entry.column ++ valueBits entry.value

def entriesWire (width : ℕ) (entries : List Logical.RationalCode.Entry) : List Bool :=
  entries.flatMap (entryWire width)

@[simp] theorem entryWire_length (width : ℕ) (entry : Logical.RationalCode.Entry) :
    (entryWire width entry).length = 2*width+2 := by simp [entryWire,valueBits]; omega

@[simp] theorem entriesWire_append (width : ℕ) (a b : List Logical.RationalCode.Entry) :
    entriesWire width (a++b) = entriesWire width a ++ entriesWire width b := by simp [entriesWire]

@[simp] theorem entriesWire_length (width : ℕ) (entries : List Logical.RationalCode.Entry) :
    (entriesWire width entries).length = entries.length*(2*width+2) := by
  induction entries with
  | nil => simp [entriesWire]
  | cons e es ih => simp only [entriesWire,List.flatMap_cons,List.length_append,entryWire_length] at *
                    simp [Nat.add_mul,Nat.add_comm,ih]

end Maxwell.Cost.SparseEmission
