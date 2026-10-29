import Maxwell.Cost.CalibrationMatrix.Horner.Affine
import Maxwell.Cost.CalibrationMatrix.Horner.Frame

namespace Maxwell.Cost.CalibrationMatrix.Horner
open Structured

abbrev firstWords {n : ℕ} (d : Data n) (words : Fin 12 → Vector (List Bool) n) := productWords d words 2 3 10 11
abbrev secondWords {n : ℕ} (d : Data n) (words : Fin 12 → Vector (List Bool) n) :=
  productWords d (firstWords d words) 10 11 4 5
abbrev roundWords {n : ℕ} (d : Data n) (words : Fin 12 → Vector (List Bool) n) :=
  affineFinalWords d (secondWords d words)

structure Fits {n : ℕ} (d : Data n) (words : Fin 12 → Vector (List Bool) n) : Prop where
  first : (d.productBuffers words 2 3 10 11).Fits
  second : (d.productBuffers (firstWords d words) 10 11 4 5).Fits
  wPositive : ∀ i, (Affine.newWPositive d.affineData (affineWords (secondWords d words)) i).bits.length ≤ addressValue d.width
  wNegative : ∀ i, (Affine.newWNegative d.affineData (affineWords (secondWords d words)) i).bits.length ≤ addressValue d.width
  xPositive : ∀ i, (Affine.newXPositive d.affineData (affineWords (secondWords d words)) i).bits.length ≤ addressValue d.width
  xNegative : ∀ i, (Affine.newXNegative d.affineData (affineWords (secondWords d words)) i).bits.length ≤ addressValue d.width

def roundCode : Code := .seq powerStepCode (.seq (selectOutputCode 4 5)
  (.seq powerStepCode (.seq (selectOutputCode 8 9) affineCode)))

def roundCost (n B : ℕ) : ℕ := 2*powerStepCost n B+affineCost n B+84*B+84

theorem Outside.of_affine {n : ℕ} {d : Data n} {s t : BitRAMState}
    (h : Affine.Outside d.affineData s t) : Outside d s t :=
  fun a ha => h a (fun i _ => ha (affinePort i))

/-- Two concrete dense products and the concrete affine pass implement one
integer Horner update, leaving the four new channels in their output arrays. -/
theorem round {n : ℕ} (d : Data n) (words : Fin 12 → Vector (List Bool) n)
    (B : ℕ) (hsized : d.Sized B) (hm : n*n < 2^B) (hn : n < 2^B) (hfit : Fits d words)
    (input : List Bool) (tape : ℕ → Bool) (count : List Bool) (hcount : addressValue count = n)
    (hcl : count.length ≤ B) (s : Store) (hw : WorkReady count B s.val)
    (hd : Stored d words s.val) (hp : Ports d 2 3 10 11 s.val) :
    ∃ cost, ∃ t : Store, cost ≤ roundCost n B ∧ Executes input tape roundCode cost s t ∧
      WorkReady count B t.val ∧ Stored d (roundWords d words) t.val ∧ Ports d 4 5 8 9 t.val ∧
      t.val.tapes 140 = s.val.tapes 140 ∧ Frame s.val t.val ∧ Outside d s.val t.val := by
  obtain ⟨c1,a,hc1,ea,haW,haD,haP,ha140,fa,ma⟩ := multiply d words 2 3 10 11
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    B hsized hm hn hfit.first input tape count hcount hcl s hw hd hp
  obtain ⟨c2,b,hc2,eb,hbW,hbD,hbP,hb140,mb,fb⟩ := select_output d (firstWords d words)
    10 11 2 3 4 5 B hsized input tape count a haW haD haP
  obtain ⟨c3,c,hc3,ec,hcW,hcD,hcP,hc140,fc,mc⟩ := multiply d (firstWords d words) 10 11 4 5
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    B hsized hm hn hfit.second input tape count hcount hcl b hbW hbD hbP
  obtain ⟨c4,e,hc4,ee,heW,heD,heP,he140,me,fe⟩ := select_output d (secondWords d words)
    4 5 10 11 8 9 B hsized input tape count c hcW hcD hcP
  obtain ⟨c5,t,hc5,et,htW,htD,htP,ht140,ft,mt⟩ := affine_pass d (secondWords d words)
    B hsized hn hfit.wPositive hfit.wNegative hfit.xPositive hfit.xNegative
    input tape count hcount hcl e heW heD heP
  refine ⟨c1+(c2+(c3+(c4+c5))),t,?_,ea.seq (eb.seq (ec.seq (ee.seq et))),htW,htD,htP,
    ht140.trans (he140.trans (hc140.trans (hb140.trans ha140))),
    ((((Frame.of_power fa).trans (Frame.of_power fb)).trans (Frame.of_power fc)).trans
      (Frame.of_power fe)).trans (Frame.of_power ft),
    ((((Outside.of_output ma).trans (Outside.of_memory mb)).trans (Outside.of_output mc)).trans
      (Outside.of_memory me)).trans (Outside.of_affine mt)⟩
  dsimp [roundCost]
  omega

end Maxwell.Cost.CalibrationMatrix.Horner
