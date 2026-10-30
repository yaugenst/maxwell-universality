import Maxwell.Continuum.RoundedIntegerRegister
import Maxwell.Continuum.RationalDataflowControlResults

/-! Fixed arithmetic for one Fourier input row. Registers 0 and 1 contain
the physical coefficient normalization and the frequency scale; 2 and 3
contain the actual calibrated real and imaginary coefficients, and 13--15
contain the decoded integer alias. No coefficient is placed in the code. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.RowArithmetic
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
open RationalAccumulator (Word)
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def bank : Finset ℕ := Finset.range 28

def products : Control :=
  .step (.binary .mul 4 1 13) (
  .step (.binary .mul 5 1 14) (
  .step (.binary .mul 6 1 15) (
  .step (.binary .mul 7 0 2) (
  .step (.binary .mul 8 0 3) .done))))

def code : Code := .seq products.code
  (.seq (RoundedInteger.code 9 7) (RoundedInteger.code 10 8))

def output (P : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update (Function.update (products.evaluate v)
    9 (RoundedInteger.result P ((v 0).mul (v 2))))
    10 (RoundedInteger.result P ((v 0).mul (v 3)))

theorem products_valid : products.Valid bank := by
  simp [products,Control.Valid,Instruction.Valid,bank]
theorem products_steps : products.steps=5 := rfl
theorem products_admissible (v : ℕ→Parts) : products.AdmissibleTrace v := by trivial
theorem products_literals (B : ℕ) : products.LiteralsFit B := by trivial

theorem products_values (v : ℕ→Parts) :
    products.evaluate v=
      Function.update (Function.update (Function.update (Function.update (Function.update v
        4 ((v 1).mul (v 13))) 5 ((v 1).mul (v 14)))
        6 ((v 1).mul (v 15))) 7 ((v 0).mul (v 2))) 8 ((v 0).mul (v 3)) := by
  simp [products,Control.evaluate,Instruction.update,BinaryOp.eval]

theorem output_frequency (P : ℕ) (v : ℕ→Parts) (i : Fin 3) :
    output P v (4+i.val)=(v 1).mul (v (13+i.val)) := by
  fin_cases i <;> simp [output,products_values]

theorem output_real (P : ℕ) (v : ℕ→Parts) :
    output P v 9=Parts.literal (((roundDyadic P ((v 0).value*(v 2).value)).numerator:ℤ):ℚ) := by
  simp only [output,Function.update_of_ne (by decide : (9:ℕ)≠10),Function.update_self,
    RoundedInteger.result,Parts.mul_value]

theorem output_imag (P : ℕ) (v : ℕ→Parts) :
    output P v 10=Parts.literal (((roundDyadic P ((v 0).value*(v 3).value)).numerator:ℤ):ℚ) := by
  simp only [output,Function.update_self,RoundedInteger.result,Parts.mul_value]

theorem output_other (P : ℕ) (v : ℕ→Parts) (i : ℕ)
    (hi : i∉({4,5,6,7,8,9,10}:Finset ℕ)) : output P v i=v i := by
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi
  simp only [output,products_values,Function.update_of_ne hi.1,Function.update_of_ne hi.2.1,
    Function.update_of_ne hi.2.2.1,Function.update_of_ne hi.2.2.2.1,
    Function.update_of_ne hi.2.2.2.2.1,Function.update_of_ne hi.2.2.2.2.2.1,
    Function.update_of_ne hi.2.2.2.2.2.2]

theorem output_good (P : ℕ) (v : ℕ→Parts) (hg : Good bank v) : Good bank (output P v) :=
  ((products.evaluate_good bank products_valid v hg (products_admissible v)).update
    9 (RoundedInteger.result_valid P _)).update 10 (RoundedInteger.result_valid P _)

theorem executes (P B : ℕ) (v : ℕ→Parts) (hw : WidthBank bank B v) (hg : Good bank v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hr : Ready bank v s)
    (hclean : DyadicFloor.Clean s.val) (hpower : Word s.val 144 (2^P)) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤2^170*(P+B+8)^2 ∧
      Ready bank (output P v) t ∧ WidthBank bank (128*(B+1)+3*P+9) (output P v) ∧
      Good bank (output P v) ∧ DyadicFloor.Clean t.val ∧ Word t.val 144 (2^P) ∧
      BinaryPrecision.Frame (DyadicFloor.StoredPower.workspace bank) s.val t.val := by
  have wt : products.WidthTrace bank (32*(B+1)) v := by
    exact products.automatic_widthTrace bank products_valid v B hw (products_literals B)
  have wg := products.evaluate_good bank products_valid v hg (products_admissible v)
  obtain ⟨c0,s0,e0,hc0,r0,f0⟩ := products.executes bank products_valid v (32*(B+1)) wt hg
    (products_admissible v) input tape s hr
  have z0 := hclean.arithmetic_frame f0
  have p0 := RationalAccumulator.word_of_eq
    (f0.tapes 144 (outside_workspace bank 144 (by decide))) hpower
  obtain ⟨c1,s1,e1,hc1,r1,w1,z1,p1,f1⟩ := RoundedInteger.executes bank P 9 7
    (by decide) (by decide) (products.evaluate v) (32*(B+1)) wt.result (wg 7 (by decide))
    input tape s0 r0 z0 p0
  let v1 := Function.update (products.evaluate v) 9
    (RoundedInteger.result P (products.evaluate v 7))
  have g1 : Good bank v1 := wg.update 9 (RoundedInteger.result_valid P _)
  obtain ⟨c2,t,e2,hc2,r2,w2,z2,p2,f2⟩ := RoundedInteger.executes bank P 10 8
    (by decide) (by decide) v1 (2*(32*(B+1))+P+3) w1 (g1 8 (by decide))
    input tape s1 r1 z1 p1
  have h7 : products.evaluate v 7=(v 0).mul (v 2) := by simp [products_values]
  have h8 : v1 8=(v 0).mul (v 3) := by simp [v1,products_values]
  have he : Function.update v1 10 (RoundedInteger.result P (v1 8))=output P v := by
    rw [h8]
    simp only [output,v1,h7]
  rw [he] at r2 w2
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,r2,?_,output_good P v hg,z2,p2,
    (f0.mono (RoundedInteger.arithmetic_workspace_subset bank)).trans (f1.trans f2)⟩
  · rw [products_steps] at hc0
    unfold operationCost at hc0
    nlinarith only [hc0,hc1,hc2,Nat.zero_le P,Nat.zero_le B]
  · convert w2 using 1
    ring

#print axioms executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.RowArithmetic
