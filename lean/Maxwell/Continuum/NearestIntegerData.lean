import Maxwell.Continuum.RoundedIntegerRegister
import Maxwell.Continuum.RationalDataflowNaturalChannels
import Maxwell.Continuum.RationalDataflowFixedWidths
import Maxwell.Continuum.RationalDataflowControlResults
import Maxwell.Logical.Rounding

/-! Half-up nearest rounding uses the stored dyadic scale and the exact
floor primitive. Registers14 and15 hold the computed half-unit. -/
namespace Maxwell.Continuum.RationalDataflow.NearestInteger
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000

def unitPart (P : ℕ) : Parts := ⟨1,0,2^P⟩
def loaded (P : ℕ) (v : ℕ→Parts) : ℕ→Parts := Function.update v 14 (unitPart P)
def tail (source : ℕ) : Control :=
  .step (.literal 15 (1/2))
    (.step (.binary .mul 14 14 15) (.step (.binary .add 14 source 14) .done))
def prepared (P source : ℕ) (v : ℕ→Parts) : ℕ→Parts := (tail source).evaluate (loaded P v)
def result (P : ℕ) (x : Parts) : Parts :=
  Parts.literal (((Maxwell.Logical.Rounding.nearest P x.value).numerator:ℤ):ℚ)
def values (P target source : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update (prepared P source v) target (result P (v source))

theorem loaded_eq (P : ℕ) (v : ℕ→Parts) :
    Function.update (Function.update v 14 (Parts.literal 1)) 14
      (NaturalChannel.replace .denominator (Parts.literal 1) (2^P))=loaded P v := by
  rw [Function.update_idem]
  rfl

theorem unitPart_value (P : ℕ) : (unitPart P).value=(2:ℚ)^(- (P:ℤ)) := by
  simp [unitPart,Parts.value,zpow_neg,zpow_natCast]

theorem unitPart_valid (P : ℕ) : (unitPart P).Valid := by exact Nat.pow_pos (by decide)

theorem unitPart_width (P W : ℕ) (hW : 1≤W) (hP : (2^P).bits.length≤W) :
    (unitPart P).Width W := by
  change (1:ℕ).bits.length≤W ∧ (0:ℕ).bits.length≤W ∧ (2^P).bits.length≤W
  exact ⟨by simpa using hW,by simp,hP⟩

theorem tail_valid (S : Finset ℕ) (source : ℕ) (hs : source∈S) (h14 : 14∈S) (h15 : 15∈S) :
    (tail source).Valid S := by simp [tail,Control.Valid,Instruction.Valid,hs,h14,h15]

theorem tail_admissible (source : ℕ) (v : ℕ→Parts) : (tail source).AdmissibleTrace v := by
  trivial

theorem tail_fits (source W : ℕ) (hW : 2≤W) : (tail source).LiteralsFit W := by
  refine ⟨?_,trivial,trivial,trivial⟩
  change (Parts.literal (1/2)).Width W
  exact (show (Parts.literal (1/2)).Width 2 by
    norm_num [Parts.literal,Parts.Width]
    decide).mono hW

theorem prepared_value (P source : ℕ) (v : ℕ→Parts) (hs14 : source≠14) (hs15 : source≠15)
    (hv : (v source).Valid) :
    (prepared P source v 14).value=(v source).value+1/(2*(2:ℚ)^P) := by
  have hpart : prepared P source v 14=(v source).add ((unitPart P).mul (Parts.literal (1/2))) := by
    simp [prepared,tail,Control.evaluate,Instruction.update,BinaryOp.eval,loaded,hs14,hs15]
  rw [hpart,Parts.add_value _ _ hv (Parts.mul_valid (unitPart_valid P) (Parts.literal_valid _)),
    Parts.mul_value,Parts.literal_value,unitPart_value]
  simp only [zpow_neg,zpow_natCast]
  ring

theorem rounded_eq (P source : ℕ) (v : ℕ→Parts) (hs14 : source≠14) (hs15 : source≠15)
    (hv : (v source).Valid) :
    RoundedInteger.result P (prepared P source v 14)=result P (v source) := by
  unfold RoundedInteger.result result roundDyadic Maxwell.Logical.Rounding.nearest
  rw [prepared_value P source v hs14 hs15 hv]
  congr 3
  have hp : (2:ℚ)^P≠0 := by positivity
  field_simp

theorem prepared_width (S : Finset ℕ) (P source W : ℕ) (hs : source∈S) (h14 : 14∈S) (h15 : 15∈S)
    (v : ℕ→Parts) (hw : WidthBank S W v) (hW : 2≤W) (hP : (2^P).bits.length≤W) :
    WidthBank S (8*(W+1)) (prepared P source v) := by
  have h := (tail source).automatic_widthTrace S (tail_valid S source hs h14 h15)
    (loaded P v) W (hw.update 14 (unitPart_width P W (by omega) hP)) (tail_fits source W hW)
  exact h.result

#print axioms rounded_eq
end Maxwell.Continuum.RationalDataflow.NearestInteger
