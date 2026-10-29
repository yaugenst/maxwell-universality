import Maxwell.Cost.DecoderParser.Terms
import Maxwell.Cost.DecoderParser.SecondPass

namespace Maxwell.Cost.DecoderParser

abbrev Row (N : ℕ) := ℚ × List (Fin N × ℚ)

def rowWire {N : ℕ} (row : Row N) : List Bool :=
  Codec.rat row.1++(Codec.nat row.2.length++row.2.flatMap termWire)

def rowTerms {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (i : Fin n) :
    List (Fin D.sampleCount × ℚ) := (D.support i).sort.map (fun j => (j,D.weight i j))

def rows {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) : List (Row D.sampleCount) :=
  (List.finRange n).map (fun i => (D.offset i,rowTerms D i))

@[simp] theorem rows_length {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) :
    (rows D).length=n := by simp [rows]

theorem target_rows {n : ℕ} (I : Target.Instance n) :
    Codec.target I=beforeRows I++(Codec.nat n++(rows I.decoder).flatMap rowWire) := by
  rw [target_beforeRows]
  congr 1
  simp [Codec.list,Codec.rat,Codec.int,rowPayload,rows,rowTerms,wire,rowWire,termWire,rationalPayload,
    List.flatMap_map,List.append_assoc]

theorem rowTerms_value {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (w : D.Messages) (i : Fin n) :
    D.offset i+termsValue D w (rowTerms D i)=D.decode w i := by
  simp only [termsValue,rowTerms,Target.WeightedDecoder.decode,List.map_map,Function.comp_def]
  congr 1
  rw [← List.sum_toFinset _ ((D.support i).sort_nodup _),Finset.sort_toFinset]

end Maxwell.Cost.DecoderParser
