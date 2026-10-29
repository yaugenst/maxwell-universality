import Maxwell.Cost.DecoderParser.Rows

namespace Maxwell.Cost.DecoderParser

def zeroMessages {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) : D.Messages :=
  fun _ => ⟨0,by positivity⟩

theorem termWidth_messages (F : Target.FixedPointFormat) (q : ℚ) (a b : F.Word) :
    termWidth F q (Codec.word F a)=termWidth F q (Codec.word F b) := by
  simp only [termWidth,Codec.word_length]

theorem termsWidth_messages {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (a b : D.Messages) (terms : List (Fin D.sampleCount × ℚ)) :
    termsWidth D a terms=termsWidth D b terms := by
  simp only [termsWidth,termWidth,Codec.word_length]

theorem termsPrice_messages {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (a b : D.Messages) (terms : List (Fin D.sampleCount × ℚ)) (A : ℕ) :
    termsPrice D a terms A=termsPrice D b terms A := by
  induction terms generalizing A with
  | nil => rfl
  | cons x xs ih =>
    simp only [termsPrice,termPrice,termWidth,Codec.word_length]
    rw [ih]

theorem rowPrice_messages {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (a b : D.Messages) (A : ℕ) (row : Row D.sampleCount) :
    rowPrice D a A row=rowPrice D b A row := by
  simp only [rowPrice,termsPrice_messages D a b,termsWidth_messages D a b]

end Maxwell.Cost.DecoderParser
