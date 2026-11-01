import Maxwell.Continuum.CalibrationParameterMachine
import Maxwell.Continuum.ContinuumCalibrationResources

/-! Source-selected outer words initialize the finite calibration inputs.
The placement radius and alias radius have separate computed registers. -/
namespace Maxwell.Continuum.Calibration.ParameterInput
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000
attribute [local irreducible] MasterConstants.exponent MasterConstants.Cs
  RealizationParameters.analysisBits RealizationParameters.inputBits

def ids : Finset ℕ := ParameterMachine.ids∪{2200,2206,2210,2221,2227}
def workspace : Finset ℕ := {0,1,2,3}∪ParameterMachine.ids
def instructions (analysis inputBits : ℕ) : List NatAssign.Instruction :=
  [.literal 4490 analysis,.literal 4491 inputBits,.literal 4492 4,.literal 4493 6,
   .literal 4494 18,.literal 4495 (2^53),.literal 4496 256,.literal 4497 8,
   .literal 4498 27,.literal 4499 2,
   .copy 2221 4400,.copy 4495 4401,.multiply 2221 4401,.multiply 2227 4401,
   .copy 2200 4423,.multiply 4490 4423,.copy 2200 4424,.multiply 4491 4424,
   .copy 2227 4420,.multiply 4492 4420,.copy 2206 4421,.multiply 4493 4421,
   .copy 4423 4402,.add 4420 4402,.add 4421 4402,.add 4494 4402,
   .copy 2210 4403,.multiply 2210 4403,.copy 4403 4422,.multiply 4422 4403,
   .copy 4423 4425,.add 4493 4425,
   .copy 4423 4426,.add 4424 4426,.add 4496 4426,
   .copy 4423 4427,.add 2200 4427,.add 4497 4427,
   .copy 4424 4428,.multiply 4499 4428,.add 4498 4428,
   .copy 4423 4429,.add 4420 4429,.add 4497 4429]

theorem valid (a b : ℕ) : ∀q∈instructions a b,q.Valid ids := by
  simp [instructions,NatAssign.Instruction.Valid,ids,ParameterMachine.ids]

theorem fields (a b : ℕ) (v : ℕ→ℕ) :
    let w := NatAssign.values (instructions a b) v
    w 4400=v 2221 ∧ w 4401=couplingRadius (v 2221) (v 2227) ∧
    w 4402=a*v 2200+4*v 2227+6*v 2206+18 ∧ w 4403=(v 2210)^4 ∧
    w 4425=a*v 2200+6 ∧ w 4426=a*v 2200+b*v 2200+256 ∧
    w 4427=a*v 2200+v 2200+8 ∧ w 4428=2*(b*v 2200)+27 ∧
    w 4429=a*v 2200+4*v 2227+8 := by
  dsimp only
  simp [instructions,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,couplingRadius]
  repeat' constructor <;> first | trivial | ring

theorem octal_bits (k : ℕ) : (Parameters.stageLength k).bits.length=3*k+1 := by
  rw [Parameters.stageLength,show (8:ℕ)=2^3 by decide,←pow_mul]
  simp [PowerOfTwo.power_bits]

theorem source_fields (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (v : ℕ→ℕ) (hlog : v 2200=RealizationParameters.logSize S)
    (hk : v 2206=RealizationParameters.stage p S hm)
    (hL : v 2221=RealizationParameters.length p S hm)
    (hd : v 2227=RealizationParameters.spacing p S hm)
    (hC : v 2210=2^MasterConstants.exponent) :
    let w := NatAssign.values (instructions (RealizationParameters.analysisBits p)
      (RealizationParameters.inputBits p)) v
    w 4400=RealizationParameters.length p S hm ∧
    w 4401=RealizationParameters.calibrationRadius p S hm ∧
    w 4402=RealizationParameters.calibrationModePrecision p S hm ∧
    w 4403=2^(4*MasterConstants.exponent) ∧
    w 4425=RealizationParameters.templatePrecision p S ∧
    w 4426=RealizationParameters.materialPrecision p S ∧
    w 4427=RealizationParameters.sourcePrecision p S ∧
    w 4428=RealizationParameters.momentPrecision p S ∧
    w 4429=RealizationParameters.calibrationPrecision p S hm := by
  dsimp only
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩ := fields (RealizationParameters.analysisBits p)
    (RealizationParameters.inputBits p) v
  rw [hlog,hd,hk] at h2
  rw [hlog] at h4 h5 h6 h7
  rw [hlog,hd] at h8
  refine ⟨h0.trans hL,?_,?_,?_,h4,h5,h6,h7,h8⟩
  · simpa only [hL,hd,RealizationParameters.calibrationRadius] using h1
  · rw [h2]
    unfold RealizationParameters.calibrationModePrecision RealizationParameters.calibrationPrecision
      RealizationParameters.scaleBits lengthBits
    rw [Codec.clog_two_succ,octal_bits]
    omega
  · rw [h3,hC,←pow_mul,Nat.mul_comm]

def width (a b B : ℕ) : ℕ := 2^(instructions a b).length*(B+a.bits.length+b.bits.length+55)
def costBound (a b B : ℕ) : ℕ := 3000*8^(instructions a b).length*(B+a.bits.length+b.bits.length+56)^2

theorem executes (a b : ℕ) (v : ℕ→ℕ) (B : ℕ) (hw : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape (NatAssign.code (instructions a b)) cost s t ∧ cost≤costBound a b B ∧
      NatAssign.Bank ids (NatAssign.values (instructions a b) v) t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈ids,(NatAssign.values (instructions a b) v i).bits.length≤width a b B) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  have lower : ∀i∈ids,4 ≤ i := by
    intro i hi
    simp only [ids,ParameterMachine.ids,Finset.mem_union,Finset.mem_Icc,
      Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  let W := B+a.bits.length+b.bits.length+54
  have wh : ∀i∈ids,(v i).bits.length≤W := fun i hi=>(hw i hi).trans (by unfold W;omega)
  have lh : ∀q∈instructions a b,q.literalWidth≤W := by
    intro q hq
    simp only [instructions,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [NatAssign.Instruction.literalWidth]
    all_goals first
      | unfold W;omega
      | exact (show _≤54 by decide +kernel).trans (by unfold W;omega)
  obtain ⟨cost,t,execution,bound,bt,st,frame⟩ := NatAssign.executes ids lower (instructions a b) (valid a b)
    v input tape s bank scratch
  refine ⟨cost,t,execution,bound.trans ?_,bt,st,?_,frame.mono ?_⟩
  · simpa only [costBound,W,Nat.add_assoc] using NatAssign.price_bound ids (instructions a b)
      (valid a b) v W wh lh
  · intro i hi
    have whi := NatAssign.values_width ids (instructions a b) (valid a b) v W wh lh i hi
    exact (Nat.le_add_right _ 1).trans (by simpa only [width,W,Nat.add_assoc] using whi)
  · change NatAssign.changes (instructions 0 0)⊆workspace
    decide +kernel

#print axioms source_fields
#print axioms executes
end Maxwell.Continuum.Calibration.ParameterInput
