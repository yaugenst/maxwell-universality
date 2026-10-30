import Maxwell.Continuum.DyadicFloorStoredPowerCost
import Maxwell.Continuum.DyadicFloorOutputWidth
import Maxwell.Continuum.DyadicFloorFrame
import Maxwell.Continuum.RationalDataflowIntegerCanonical

/-! A fixed shared-bank program rounds an arbitrary valid rational register
to the numerator of a dyadic, then puts that integer in canonical signed
form. Its scale is an actually stored word and every division and signed
normalization step is charged. -/
namespace Maxwell.Continuum.RationalDataflow.RoundedInteger
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word)
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def code (target source : ℕ) : Code :=
  .seq (DyadicFloor.StoredPower.code target source) (IntegerCanonical.code target target)

def result (P : ℕ) (x : Parts) : Parts :=
  Parts.literal (((roundDyadic P x.value).numerator : ℤ) : ℚ)

theorem result_valid (P : ℕ) (x : Parts) : (result P x).Valid := by
  exact Parts.literal_valid _

theorem result_value (P : ℕ) (x : Parts) :
    (result P x).value = (((roundDyadic P x.value).numerator : ℤ) : ℚ) := by
  exact Parts.literal_value _

theorem result_width (P B : ℕ) (x : Parts) (hx : x.Valid) (hw : x.Width B) :
    (result P x).Width (2*B+P+3) := by
  have he : IntegerCanonical.result (DyadicFloor.result P x)=result P x := by
    rw [IntegerCanonical.result_eq_literal_value _ rfl,DyadicFloor.result_value P x hx]
    rfl
  have hh := IntegerCanonical.result_width (2*B+P+2) _ (DyadicFloor.result_raw_width P B x hw)
  simpa only [he,Nat.add_assoc] using hh

theorem arithmetic_workspace_subset (S : Finset ℕ) :
    RationalDataflow.workspace S ⊆ DyadicFloor.StoredPower.workspace S := by
  intro i hi
  exact Finset.mem_insert_of_mem (by
    rcases Finset.mem_union.mp hi with hz|hr
    · exact Finset.mem_union_left _ (by
        simp only [Finset.mem_insert,Finset.mem_singleton] at hz ⊢
        tauto)
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_left _ hr)))

theorem executes (S : Finset ℕ) (P target source : ℕ) (ht : target∈S) (hs' : source∈S)
    (v : ℕ→Parts) (B : ℕ) (hw : WidthBank S B v) (hx : (v source).Valid)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hr : Ready S v s)
    (hclean : DyadicFloor.Clean s.val) (hpower : Word s.val 144 (2^P)) :
    ∃cost t,Executes input tape (code target source) cost s t ∧ cost≤2^145*(P+B+6)^2 ∧
      Ready S (Function.update v target (result P (v source))) t ∧
      WidthBank S (2*B+P+3) (Function.update v target (result P (v source))) ∧
      DyadicFloor.Clean t.val ∧ Word t.val 144 (2^P) ∧
      BinaryPrecision.Frame (DyadicFloor.StoredPower.workspace S) s.val t.val := by
  obtain ⟨c0,s0,e0,hc0,r0,z0,p0,f0⟩ := DyadicFloor.StoredPower.executes S P target source
    ht hs' v B hw hx input tape s hr hclean hpower
  let v0 := Function.update v target (DyadicFloor.result P (v source))
  have w0 : WidthBank S (2*B+P+2) v0 := by
    intro i hi
    by_cases he : i=target
    · subst i
      simpa only [v0,Function.update_self] using
        DyadicFloor.result_raw_width P B (v source) (hw source hs')
    · simpa only [v0,Function.update_of_ne he] using (hw i hi).mono (by omega)
  obtain ⟨c1,t,e1,hc1,r1,f1⟩ := IntegerCanonical.executes S target target ht ht
    v0 (2*B+P+2) w0 input tape s0 r0
  have he : IntegerCanonical.result (v0 target)=result P (v source) := by
    rw [show v0 target=DyadicFloor.result P (v source) from Function.update_self ..]
    rw [IntegerCanonical.result_eq_literal_value _ rfl,DyadicFloor.result_value P (v source) hx]
    rfl
  have hvalues : Function.update v0 target (IntegerCanonical.result (v0 target))=
      Function.update v target (result P (v source)) := by
    rw [he]
    exact Function.update_idem ..
  rw [hvalues] at r1
  refine ⟨c0+c1,t,e0.seq e1,?_,r1,?_,z0.arithmetic_frame f1,
    RationalAccumulator.word_of_eq (f1.tapes 144 (outside_workspace S 144 (by decide))) p0,
    f0.trans (f1.mono (arithmetic_workspace_subset S))⟩
  · have hc0' := hc0.trans (DyadicFloor.costBound_polynomial P B)
    unfold operationCost at hc1
    nlinarith only [hc0',hc1,Nat.zero_le P,Nat.zero_le B]
  · intro i hi
    by_cases hi' : i=target
    · subst i
      simpa only [Function.update_self] using result_width P B (v source) hx (hw source hs')
    · simpa only [Function.update_of_ne hi'] using (hw i hi).mono (by omega)

#print axioms executes
end Maxwell.Continuum.RationalDataflow.RoundedInteger
