import Maxwell.Continuum.StoredSourceAmplitude
import Maxwell.Continuum.RationalDataflowNaturalChannels
import Maxwell.Continuum.RationalDataflowControlResults

/-! The common source multiplier is computed from actual calibrated raw
parts and the retained original source-scale numerator and denominator. -/
namespace Maxwell.Continuum.SourcePayload
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def scaleParts (N D : ℕ) : Parts:=⟨N,0,D⟩
def multiplierControl : Control:=.step (.inverse 13 1)
  (.step (.binary .mul 13 4 13) (.step (.inverse 12 12) (.step (.binary .mul 13 13 12) .done)))
def multiplierCode : Code:=.seq (Instruction.literal 12 0).code
  (.seq (NaturalChannel.code .positive 506 12)
    (.seq (NaturalChannel.code .denominator 507 12) multiplierControl.code))
def multiplierValues (N D : ℕ) (v : ℕ→Parts) : ℕ→Parts:=
  multiplierControl.evaluate (Function.update v 12 (scaleParts N D))

theorem scaleParts_value (N D : ℕ) : (scaleParts N D).value=(N:ℚ)/D:=by simp [scaleParts,Parts.value]
theorem scaleParts_nonzero {N D : ℕ} (hN : 0<N) (hD : 0<D) : (scaleParts N D).value≠0:=by
  rw [scaleParts_value]
  exact div_ne_zero (by exact_mod_cast hN.ne') (by exact_mod_cast hD.ne')
theorem multiplier_valid : multiplierControl.Valid bank:=by
  simp [multiplierControl,Control.Valid,Instruction.Valid,bank]
theorem multiplier_admissible (N D : ℕ) (v : ℕ→Parts) (mode : (v 1).value≠0)
    (hN : 0<N) (hD : 0<D) :
    multiplierControl.AdmissibleTrace (Function.update v 12 (scaleParts N D)):=by
  simp only [multiplierControl,Control.AdmissibleTrace,Instruction.Admissible,Instruction.update,
    Function.update_self,Function.update_of_ne (by decide : (1:ℕ)≠12),
    Function.update_of_ne (by decide : (12:ℕ)≠13),and_true]
  exact ⟨mode,trivial,scaleParts_nonzero hN hD⟩

theorem multiplier_value (N D : ℕ) (v : ℕ→Parts) (good : Good bank v)
    (mode : (v 1).value≠0) (hN : 0<N) (hD : 0<D) :
    (multiplierValues N D v 13).value=((v 4).value/(v 1).value)/((N:ℚ)/D):=by
  simp only [multiplierValues,multiplierControl,Control.evaluate,Instruction.update,BinaryOp.eval,
    Function.update_self,Function.update_of_ne (by decide : (1:ℕ)≠12),
    Function.update_of_ne (by decide : (4:ℕ)≠12),Function.update_of_ne (by decide : (4:ℕ)≠13),
    Function.update_of_ne (by decide : (12:ℕ)≠13),Function.update_of_ne (by decide : (13:ℕ)≠12),
    Parts.mul_value,Parts.inverse_value _ (good 1 (by decide)) mode,
    Parts.inverse_value _ (show (scaleParts N D).Valid from hD) (scaleParts_nonzero hN hD),scaleParts_value,div_eq_mul_inv]

theorem multiplier_executes (N D B : ℕ) (hB : 2≤B) (hN : 0<N) (hD : 0<D)
    (numWidth : N.bits.length≤B) (denWidth : D.bits.length≤B)
    (v : ℕ→Parts) (width : WidthBank bank B v) (good : Good bank v) (mode : (v 1).value≠0)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (ready : Ready bank v s)
    (num : Word s.val 506 N) (den : Word s.val 507 D) :
    ∃cost t,Executes input tape multiplierCode cost s t ∧cost≤2^120*(B+2)^2 ∧
      Ready bank (multiplierValues N D v) t ∧ Good bank (multiplierValues N D v) ∧
      WidthBank bank (16*(B+1)) (multiplierValues N D v) ∧
      BinaryPrecision.Frame (workspace bank) s.val t.val := by
  have zeroWidth : (Parts.literal 0).Width B:=
    (show (Parts.literal 0).Width 1 by norm_num [Parts.Width,Parts.literal]).mono (by omega)
  obtain ⟨c0,a,e0,hc0,ra,f0⟩:=(Instruction.literal 12 0).executes bank (show 12∈bank from by decide) v B width zeroWidth input tape s ready
  let v0:=Function.update v 12 (Parts.literal 0)
  obtain ⟨c1,b,e1,hc1,rb,f1⟩:=NaturalChannel.executes bank .positive 506 12 (by decide) (by decide)
    v0 N.bits input tape a ra (word_of_eq (f0.tapes 506 (outside_workspace bank 506 (by decide))) num)
  let v1:=Function.update v 12 (scaleParts N 1)
  have veq : Function.update v0 12 (NaturalChannel.replace .positive (v0 12) (addressValue N.bits))=v1:=by
    simp [v0,v1,NaturalChannel.replace,Parts.literal,scaleParts]
  rw [veq] at rb
  obtain ⟨c2,c,e2,hc2,rc,f2⟩:=NaturalChannel.executes bank .denominator 507 12 (by decide) (by decide)
    v1 D.bits input tape b rb (word_of_eq ((f1.tapes 507 (by decide)).trans
      (f0.tapes 507 (outside_workspace bank 507 (by decide)))) den)
  let loaded:=Function.update v 12 (scaleParts N D)
  have veq2 : Function.update v1 12 (NaturalChannel.replace .denominator (v1 12) (addressValue D.bits))=loaded:=by
    simp [v1,loaded,NaturalChannel.replace,scaleParts]
  rw [veq2] at rc
  have loadedWidth : WidthBank bank B loaded:=width.update 12 ⟨numWidth,by simp [scaleParts],denWidth⟩
  have loadedGood : Good bank loaded:=good.update 12 hD
  have trace:=multiplierControl.automatic_widthTrace bank multiplier_valid loaded B loadedWidth (by trivial)
  have admissible:=multiplier_admissible N D v mode hN hD
  obtain ⟨c3,t,e3,hc3,rt,f3⟩:=multiplierControl.executes bank multiplier_valid loaded (16*(B+1))
    trace loadedGood admissible input tape c rc
  have lift1 : ({NaturalChannel.port .positive 12}:Finset ℕ)⊆workspace bank:=by decide
  have lift2 : ({NaturalChannel.port .denominator 12}:Finset ℕ)⊆workspace bank:=by decide
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,rt,
    multiplierControl.evaluate_good bank multiplier_valid loaded loadedGood admissible,trace.result,
    f0.trans ((f1.mono lift1).trans ((f2.mono lift2).trans f3))⟩
  have channel0 : dataValues v0 (NaturalChannel.port .positive 12)=0:=by
    simp [v0,NaturalChannel.port,Parts.literal]
  have channel1 : dataValues v1 (NaturalChannel.port .denominator 12)=1:=by
    simp [v1,NaturalChannel.port,scaleParts]
  rw [channel0] at hc1
  rw [channel1] at hc2
  change c3≤4*operationCost (16*(B+1))+1 at hc3
  unfold operationCost at hc0 hc3
  simp only [show (0:ℕ).bits.length=0 from rfl,show (1:ℕ).bits.length=1 from rfl] at hc1 hc2
  nlinarith only [hc0,hc1,hc2,hc3,numWidth,denWidth,Nat.zero_le B]

#print axioms multiplier_executes
end Maxwell.Continuum.SourcePayload
