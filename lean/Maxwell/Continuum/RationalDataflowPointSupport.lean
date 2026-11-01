import Maxwell.Continuum.RationalDataflowQuotientExpression
import Maxwell.Continuum.RationalDataflowExpressionFrame

/-! Fixed finite point supports compiled to rational arithmetic and actual
zero tests. The input coordinates remain available for subsequent array rows.
This supplies sparse forcing values without assuming their coefficient table. -/
namespace Maxwell.Continuum.RationalDataflow.PointSupport
open Maxwell.Cost Maxwell.Cost.Structured PolynomialExpression
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

abbrev Point := List (ℕ × ℚ)
abbrev Support := List (Point × ℚ)

def distance : Point → PolynomialExpression
  | [] => .literal 0
  | (i,q)::rest =>
      let d := PolynomialExpression.binary .sub (.inputRegister i) (.literal q)
      .binary .add (.binary .mul d d) (distance rest)

def Matches (p : Point) (v : ℕ → ℚ) : Prop := ∀a∈p,v a.1=a.2
instance (p : Point) (v : ℕ → ℚ) : Decidable (Matches p v) :=
  inferInstanceAs (Decidable (∀a∈p,v a.1=a.2))

def value (support : Support) (v : ℕ → ℚ) : ℚ :=
  (support.map (fun p => if Matches p.1 v then p.2 else 0)).sum

def pointControl (p : Point) (weight : ℚ) (base : ℕ) : Control :=
  ((distance p).control (base+1)).andThen
    (.positive (base+1) .done
      (.step (.literal (base+1) weight) (.step (.binary .add base base (base+1)) .done)))

def traversal (base : ℕ) : Support → Control
  | [] => .done
  | (p,w)::rest => (pointControl p w base).andThen (traversal base rest)

def control (support : Support) (base : ℕ) : Control :=
  .step (.literal base 0) (traversal base support)

def Scoped (support : Support) (base : ℕ) : Prop :=
  ∀p∈support,(distance p.1).Scoped base
def LiteralsFit (support : Support) (B : ℕ) : Prop :=
  ∀p∈support,(distance p.1).LiteralsFit B ∧ (Parts.literal p.2).Width B
def space (support : Support) : ℕ := (support.map (fun p => (distance p.1).nodes)).sum
def registers (support : Support) (base : ℕ) : Finset ℕ := Finset.range (base+space support+2)
def width (support : Support) (base B : ℕ) : ℕ := 2^(control support base).steps*(B+1)
def costCoefficient (support : Support) (base : ℕ) : ℕ :=
  (control support base).steps*2^100*(2^(control support base).steps+3)^2+1

theorem distance_nonneg (p : Point) (v : ℕ → ℚ) : 0≤(distance p).evaluate v := by
  induction p with
  | nil => simp [distance,PolynomialExpression.evaluate]
  | cons a rest ih =>
    simp only [distance,PolynomialExpression.evaluate,binaryValue]
    exact add_nonneg (mul_self_nonneg _) ih

theorem distance_zero (p : Point) (v : ℕ → ℚ) :
    (distance p).evaluate v=0 ↔ Matches p v := by
  induction p with
  | nil => simp [distance,PolynomialExpression.evaluate,Matches]
  | cons a rest ih =>
    have hn := distance_nonneg rest v
    simp only [distance,PolynomialExpression.evaluate,binaryValue,Matches,List.mem_cons,
      forall_eq_or_imp] at ih ⊢
    constructor
    · intro h
      have hs : (v a.1-a.2)*(v a.1-a.2)=0 := by nlinarith [mul_self_nonneg (v a.1-a.2)]
      have he : v a.1=a.2 := by rcases mul_eq_zero.mp hs with h|h <;> linarith
      exact ⟨he,ih.mp (by nlinarith [mul_self_nonneg (v a.1-a.2)])⟩
    · rintro ⟨he,hr⟩
      rw [he,sub_self,zero_mul,zero_add,ih.mpr hr]

theorem distance_scoped (p : Point) (base : ℕ) (h : ∀a∈p,a.1<base) :
    (distance p).Scoped base := by
  induction p with
  | nil => trivial
  | cons a rest ih =>
    exact ⟨⟨⟨h a (by simp),trivial⟩,⟨h a (by simp),trivial⟩⟩,
      ih (fun b hb => h b (by simp [hb]))⟩

theorem value_congr (support : Support) (base : ℕ) (h : Scoped support base)
    (v w : ℕ → ℚ) (same : ∀i,i<base → v i=w i) : value support v=value support w := by
  unfold value
  congr 1
  apply List.map_congr_left
  intro p hp
  have he := (distance p.1).evaluate_congr base (h p hp) v w same
  have hm : Matches p.1 v ↔ Matches p.1 w := by
    rw [← distance_zero,← distance_zero,he]
  simp only [hm]

theorem point_result (p : Point) (weight : ℚ) (base : ℕ)
    (hscope : (distance p).Scoped base) (v : ℕ → ℚ) :
    (pointControl p weight base).rationalEvaluate v base=
      v base+(if Matches p v then weight else 0) ∧
    ∀i,i<base → (pointControl p weight base).rationalEvaluate v i=v i := by
  let u := ((distance p).control (base+1)).rationalEvaluate v
  have result := (distance p).rational_result (base+1) (hscope.mono (by omega)) v
  rw [← PolynomialExpression.control_rational] at result
  change u (base+1)=(distance p).evaluate v ∧ (∀i,i<base+1 → u i=v i) at result
  let tail := Control.positive (base+1) .done
    (.step (.literal (base+1) weight) (.step (.binary .add base base (base+1)) .done))
  simp only [pointControl,Control.andThen_rational]
  change tail.rationalEvaluate u base=_ ∧ ∀i,i<base → tail.rationalEvaluate u i=v i
  dsimp only [tail]
  by_cases hm : Matches p v
  · have hz := (distance_zero p v).mpr hm
    simp only [Control.rationalEvaluate,result.1,hz,lt_self_iff_false,ite_false,
      Instruction.rationalUpdate,Function.update_self,Function.update_of_ne (by omega : base≠base+1),
      result.2 base (by omega),hm,ite_true]
    refine ⟨trivial,?_⟩
    intro i hi
    simp only [Function.update_of_ne (by omega : i≠base),Function.update_of_ne (by omega : i≠base+1)]
    exact result.2 i (by omega)
  · have hp : 0<(distance p).evaluate v :=
      lt_of_le_of_ne (distance_nonneg p v) (Ne.symm (fun hz => hm ((distance_zero p v).mp hz)))
    simp only [Control.rationalEvaluate,result.1,hp,ite_true,hm,ite_false,add_zero]
    exact ⟨result.2 base (by omega),fun i hi => result.2 i (by omega)⟩

theorem traversal_result (support : Support) (base : ℕ) (hscope : Scoped support base)
    (v : ℕ → ℚ) :
    (traversal base support).rationalEvaluate v base=v base+value support v ∧
    ∀i,i<base → (traversal base support).rationalEvaluate v i=v i := by
  induction support generalizing v with
  | nil => simp [traversal,Control.rationalEvaluate,value]
  | cons p rest ih =>
    have hp := point_result p.1 p.2 base (hscope p (by simp)) v
    have hr : Scoped rest base := fun q hq => hscope q (by simp [hq])
    have hh := ih hr ((pointControl p.1 p.2 base).rationalEvaluate v)
    have values := value_congr rest base hr _ v hp.2
    simp only [traversal,Control.andThen_rational]
    refine ⟨?_,fun i hi => (hh.2 i hi).trans (hp.2 i hi)⟩
    rw [hh.1,hp.1,values]
    simp only [value,List.map_cons,List.sum_cons]
    ring

theorem rational_result (support : Support) (base : ℕ) (hscope : Scoped support base)
    (v : ℕ → ℚ) :
    (control support base).rationalEvaluate v base=value support v ∧
    ∀i,i<base → (control support base).rationalEvaluate v i=v i := by
  let z := Function.update v base 0
  have same (i : ℕ) (hi : i<base) : z i=v i := Function.update_of_ne (by omega) _ _
  have result := traversal_result support base hscope z
  change (traversal base support).rationalEvaluate z base=_ ∧ _
  rw [result.1,value_congr support base hscope z v same]
  simp only [z,Function.update_self,zero_add]
  exact ⟨trivial,fun i hi => (result.2 i hi).trans (same i hi)⟩

theorem point_valid (p : Point) (weight : ℚ) (base limit : ℕ)
    (hscope : (distance p).Scoped base) (hspace : base+1+(distance p).nodes≤limit) :
    (pointControl p weight base).Valid (Finset.range limit) := by
  have pos := (distance p).nodes_pos
  exact Control.andThen_valid _ _ _
    ((distance p).control_valid (base+1) limit (hscope.mono (by omega)) hspace) (by
      simp [Control.Valid,Instruction.Valid]
      omega)

theorem traversal_valid (support : Support) (base limit : ℕ)
    (hscope : Scoped support base) (hspace : ∀p∈support,base+1+(distance p.1).nodes≤limit) :
    (traversal base support).Valid (Finset.range limit) := by
  induction support with
  | nil => trivial
  | cons p rest ih =>
    exact Control.andThen_valid _ _ _
      (point_valid p.1 p.2 base limit (hscope p (by simp)) (hspace p (by simp)))
      (ih (fun q hq => hscope q (by simp [hq])) (fun q hq => hspace q (by simp [hq])))

theorem valid (support : Support) (base : ℕ) (hscope : Scoped support base) :
    (control support base).Valid (registers support base) := by
  refine ⟨by simp [Instruction.Valid,registers];omega,
    traversal_valid support base (base+space support+2) hscope ?_⟩
  intro p hp
  have hn : (distance p.1).nodes≤space support :=
    List.single_le_sum (fun n _ => Nat.zero_le n) _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  omega

theorem point_admissible (p : Point) (weight : ℚ) (base : ℕ) (v : ℕ → Parts) :
    (pointControl p weight base).AdmissibleTrace v := by
  apply Control.andThen_admissible
  · exact (distance p).control_admissible _ _
  · simp [Control.AdmissibleTrace,Instruction.Admissible]

theorem traversal_admissible (support : Support) (base : ℕ) (v : ℕ → Parts) :
    (traversal base support).AdmissibleTrace v := by
  induction support generalizing v with
  | nil => trivial
  | cons p rest ih => exact Control.andThen_admissible _ _ _ (point_admissible _ _ _ _) (ih _)

theorem admissible (support : Support) (base : ℕ) (v : ℕ → Parts) :
    (control support base).AdmissibleTrace v := ⟨trivial,traversal_admissible _ _ _⟩

theorem point_literals (p : Point) (weight : ℚ) (base B : ℕ) (hB : 1≤B)
    (hp : (distance p).LiteralsFit B) (hw : (Parts.literal weight).Width B) :
    (pointControl p weight base).LiteralsFit B :=
  Control.andThen_literals _ _ B ((distance p).control_literals _ _ hB hp)
    ⟨trivial,hw,trivial,trivial⟩

theorem traversal_literals (support : Support) (base B : ℕ) (hB : 1≤B)
    (hl : LiteralsFit support B) : (traversal base support).LiteralsFit B := by
  induction support with
  | nil => trivial
  | cons p rest ih =>
    exact Control.andThen_literals _ _ B
      (point_literals p.1 p.2 base B hB (hl p (by simp)).1 (hl p (by simp)).2)
      (ih (fun q hq => hl q (by simp [hq])))

theorem point_keep (p : Point) (weight : ℚ) (base : ℕ) (v : ℕ → Parts)
    (i : ℕ) (hi : i<base) : (pointControl p weight base).evaluate v i=v i := by
  simp only [pointControl,Control.andThen_evaluate,Control.evaluate]
  split_ifs
  · exact (distance p).control_keep (base+1) v i (by omega)
  · simp only [Instruction.update,Function.update_of_ne (by omega : i≠base),
      Function.update_of_ne (by omega : i≠base+1)]
    exact (distance p).control_keep (base+1) v i (by omega)

theorem traversal_keep (support : Support) (base : ℕ) (v : ℕ → Parts)
    (i : ℕ) (hi : i<base) : (traversal base support).evaluate v i=v i := by
  induction support generalizing v with
  | nil => rfl
  | cons p rest ih =>
    rw [traversal,Control.andThen_evaluate,ih,point_keep _ _ _ _ i hi]

theorem control_keep (support : Support) (base : ℕ) (v : ℕ → Parts)
    (i : ℕ) (hi : i<base) : (control support base).evaluate v i=v i := by
  change (traversal base support).evaluate (Function.update v base (Parts.literal 0)) i=v i
  rw [traversal_keep _ _ _ i hi,Function.update_of_ne (by omega : i≠base)]

theorem point_accumulator_width (p : Point) (weight : ℚ) (base B C : ℕ)
    (v : ℕ → Parts) (hv : (v base).Width B) (hw : (Parts.literal weight).Width C) :
    ((pointControl p weight base).evaluate v base).Width (B+C+1) := by
  have keep := (distance p).control_keep (base+1) v base (by omega)
  simp only [pointControl,Control.andThen_evaluate,Control.evaluate]
  split_ifs
  · rw [keep]
    exact hv.mono (by omega)
  · simp only [Instruction.update,Function.update_self,
      Function.update_of_ne (by omega : base≠base+1),keep]
    exact hv.add hw

theorem traversal_accumulator_width (support : Support) (base B C : ℕ) (v : ℕ → Parts)
    (hv : (v base).Width B) (hw : ∀p∈support,(Parts.literal p.2).Width C) :
    ((traversal base support).evaluate v base).Width (B+support.length*(C+1)) := by
  induction support generalizing v B with
  | nil => simpa only [traversal,Control.evaluate,List.length_nil,zero_mul,add_zero] using hv
  | cons p rest ih =>
    rw [traversal,Control.andThen_evaluate]
    have h := ih (B+C+1) ((pointControl p.1 p.2 base).evaluate v)
      (point_accumulator_width p.1 p.2 base B C v hv (hw p (by simp)))
      (fun q hq => hw q (by simp [hq]))
    convert h using 1
    simp only [List.length_cons]
    ring

theorem accumulator_width (support : Support) (base C : ℕ) (v : ℕ → Parts)
    (hw : ∀p∈support,(Parts.literal p.2).Width C) :
    ((control support base).evaluate v base).Width (1+support.length*(C+1)) := by
  apply traversal_accumulator_width support base 1 C (Function.update v base (Parts.literal 0))
  · rw [Function.update_self]
    norm_num [Parts.Width,Parts.literal]
  · exact hw

theorem executes (support : Support) (base B : ℕ) (hscope : Scoped support base)
    (hB : 1≤B) (hl : LiteralsFit support B) (v : ℕ → Parts)
    (hw : WidthBank (registers support base) B v) (hg : Good (registers support base) v)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : Ready (registers support base) v s) :
    ∃cost t output,Executes input tape (control support base).code cost s t ∧
      cost≤costCoefficient support base*(B+1)^2 ∧
      Ready (registers support base) output t ∧ Good (registers support base) output ∧
      WidthBank (registers support base) (width support base B) output ∧
      (output base).value=value support (valueBank v) ∧
      (∀i,i<base → output i=v i) ∧ output=(control support base).evaluate v ∧
      BinaryPrecision.Frame (workspace (registers support base)) s.val t.val := by
  have hv := valid support base hscope
  have ha := admissible support base v
  have zero := (show (Parts.literal 0).Width 1 by change 0≤1 ∧ 0≤1 ∧ 1≤1;omega).mono hB
  have trace := (control support base).automatic_widthTrace (registers support base) hv v B hw
    ⟨zero,traversal_literals support base B hB hl⟩
  obtain ⟨c,t,e,hc,ready,frame⟩ := (control support base).executes (registers support base)
    hv v (width support base B) trace hg ha input tape s hs
  have values := (control support base).evaluate_value (registers support base) hv v hg ha
  have result := rational_result support base hscope (valueBank v)
  refine ⟨c,t,(control support base).evaluate v,e,?_,ready,
    (control support base).evaluate_good _ hv v hg ha,trace.result,
    (congrFun values base).trans result.1,
    fun i hi => control_keep support base v i hi,rfl,frame⟩
  have bound : width support base B+3≤(2^(control support base).steps+3)*(B+1) := by
    unfold width
    nlinarith
  have squared := Nat.pow_le_pow_left bound 2
  unfold operationCost at hc
  unfold costCoefficient
  have h1 : 1≤(B+1)^2 := by nlinarith
  nlinarith only [hc,squared,h1]

#print axioms executes
end Maxwell.Continuum.RationalDataflow.PointSupport
