import Maxwell.Cost.CalibrationMatrix.Horner.Round

/-! One actual matrix product and affine array pass for a shared-denominator Neumann step. -/
namespace Maxwell.Continuum.Calibration.NeumannMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix Maxwell.Cost.CalibrationMatrix.Horner
set_option maxHeartbeats 1500000

abbrev productWords {n : ℕ} (d : Horner.Data n) (words : Fin 12→Vector (List Bool) n) :=
  Horner.productWords d words 10 11 5 4

abbrev roundWords {n : ℕ} (d : Horner.Data n) (words : Fin 12→Vector (List Bool) n) :=
  affineFinalWords d (productWords d words)

structure Fits {n : ℕ} (d : Horner.Data n) (words : Fin 12→Vector (List Bool) n) : Prop where
  product : (d.productBuffers words 10 11 5 4).Fits
  wPositive : ∀ i, (Affine.newWPositive d.affineData (affineWords (productWords d words)) i).bits.length≤addressValue d.width
  wNegative : ∀ i, (Affine.newWNegative d.affineData (affineWords (productWords d words)) i).bits.length≤addressValue d.width
  xPositive : ∀ i, (Affine.newXPositive d.affineData (affineWords (productWords d words)) i).bits.length≤addressValue d.width
  xNegative : ∀ i, (Affine.newXNegative d.affineData (affineWords (productWords d words)) i).bits.length≤addressValue d.width

def roundCode : Code := .seq powerStepCode (.seq (selectInputCode 4 5)
  (.seq (selectOutputCode 8 9) affineCode))

def roundCost (n B : ℕ) : ℕ := powerStepCost n B+affineCost n B+84*B+84

theorem round {n : ℕ} (d : Horner.Data n) (words : Fin 12→Vector (List Bool) n)
    (B : ℕ) (hsized : d.Sized B) (hm : n*n<2^B) (hn : n<2^B) (hfit : Fits d words)
    (input : List Bool) (tape : ℕ→Bool) (count : List Bool) (hcount : addressValue count=n)
    (hcl : count.length≤B) (s : Store) (hw : WorkReady count B s.val)
    (hd : Stored d words s.val) (hp : Ports d 10 11 5 4 s.val) :
    ∃ cost t, cost≤roundCost n B ∧ Executes input tape roundCode cost s t ∧
      WorkReady count B t.val ∧ Stored d (roundWords d words) t.val ∧ Ports d 4 5 8 9 t.val ∧
      t.val.tapes 140=s.val.tapes 140 ∧ Outside d s.val t.val := by
  obtain ⟨c1,a,hc1,ea,haW,haD,haP,ha140,_,ma⟩ := multiply d words 10 11 5 4
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    B hsized hm hn hfit.product input tape count hcount hcl s hw hd hp
  obtain ⟨c2,b,hc2,eb,hbW,hbD,hbP,hb140,mb,_⟩ := select_input d (productWords d words)
    5 4 10 11 4 5 B hsized input tape count a haW haD haP
  obtain ⟨c3,c,hc3,ec,hcW,hcD,hcP,hc140,mc,_⟩ := select_output d (productWords d words)
    4 5 10 11 8 9 B hsized input tape count b hbW hbD hbP
  obtain ⟨c4,t,hc4,et,htW,htD,htP,ht140,_,mt⟩ := affine_pass d (productWords d words)
    B hsized hn hfit.wPositive hfit.wNegative hfit.xPositive hfit.xNegative
    input tape count hcount hcl c hcW hcD hcP
  refine ⟨c1+(c2+(c3+c4)),t,?_,ea.seq (eb.seq (ec.seq et)),htW,htD,htP,
    ht140.trans (hc140.trans (hb140.trans ha140)),
    (((Outside.of_output ma).trans (Outside.of_memory mb)).trans (Outside.of_memory mc)).trans
      (Outside.of_affine mt)⟩
  unfold roundCost
  omega

#print axioms round

end Maxwell.Continuum.Calibration.NeumannMachine
