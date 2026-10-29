import Maxwell.Cost.CalibrationMatrix.Product
import Maxwell.Cost.RationalCanonical.Transfer
import Maxwell.Cost.RationalAccumulator.Reset
import Maxwell.Cost.RationalAccumulator.Move
import Maxwell.Cost.WordCall
import Maxwell.Cost.NormalizeCoefficient.Load

/-! Products of runtime descriptor words for decoder coefficients. Every
factor is read from a fixed tape; zero factors follow the actual padded
integer multiplication program. -/
namespace Maxwell.Cost.PhysicalDecoder.Product
open Structured RationalAccumulator

def stepCode (source target : ℕ) : Code :=
  .seq (.call (WordTransfer.clone source 1))
    (.seq (CalibrationMatrix.productCode target) (.call (TapeOps.clear 1)))

theorem step (source target : ℕ) (hs : 37 ≤ source) (ht : 30 ≤ target) (ht' : target ≤ 36)
    (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (a : ℕ) (s : Store)
    (hword : Word s.val source a) (hbank : Bank s.val v) (hr : Scratch s.val 0) :
    ∃ cost t, cost ≤ 2000*(a.bits.length+(v target).bits.length+3)^2 ∧
      Executes input tape (stepCode source target) cost s t ∧
      Bank t.val (Function.update v target (a*v target)) ∧ Scratch t.val 0 ∧
      RationalAccumulator.Frame s.val t.val := by
  obtain ⟨so,hso⟩ := hword
  obtain ⟨xo,hxo⟩ := (zero_word_iff_blank _ _).mp hr.2.1
  obtain ⟨u,eu,ut,uf⟩ := WordCall.clone source 1 (by omega) input tape a.bits so xo s hso hxo
  have uw : Word u.val 1 a := ⟨xo,by simp [ut]⟩
  have ub : Bank u.val v := fun i hi hi' => word_of_eq
    (uf.2.2.2.2.2.1 i (by omega) (by omega)) (hbank i hi hi')
  have ur : Scratch u.val a := ⟨blank_of_eq (uf.2.2.2.2.2.1 0 (by omega) (by omega)) hr.1,uw,
    blank_of_eq (uf.2.2.2.2.2.1 2 (by omega) (by omega)) hr.2.2.1,
    blank_of_eq (uf.2.2.2.2.2.1 3 (by omega) (by omega)) hr.2.2.2⟩
  have fu : RationalAccumulator.Frame s.val u.val := by
    refine ⟨uf.1,uf.2.1,uf.2.2.1,uf.2.2.2.1,uf.2.2.2.2.1,?_,
      fun i _ h24 h25 h26 h27 => uf.2.2.2.2.2.2 i h24 h25 h26 h27⟩
    intro i hi _
    simp [ut,show i ≠ 1 by omega]
  obtain ⟨c,w,hc,ew,wb,wr,wf⟩ := CalibrationMatrix.product target ht ht' input tape v a u ub ur
  obtain ⟨t,et,tb,tr,tf⟩ := clear_one input tape _ a w wb wr
  refine ⟨(15*a.bits.length+17)+(c+(6*a.bits.length+4)),t,?_,eu.seq (ew.seq et),tb,tr,
    fu.trans (wf.trans tf)⟩
  nlinarith [Nat.zero_le (a.bits.length*(v target).bits.length)]

def factorsCode (target : ℕ) : List ℕ → Code
  | [] => .skip
  | source :: rest => .seq (stepCode source target) (factorsCode target rest)

def bitSum (sources : List ℕ) (values : ℕ → ℕ) : ℕ :=
  (sources.map (fun i => (values i).bits.length)).sum

theorem factors (sources : List ℕ) (target : ℕ)
    (hs : ∀ i ∈ sources,37 ≤ i) (ht : 30 ≤ target) (ht' : target ≤ 36)
    (values v : ℕ → ℕ) (B : ℕ) (hwidth : bitSum sources values+(v target).bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hw : ∀ i ∈ sources,Word s.val i (values i)) (hb : Bank s.val v) (hr : Scratch s.val 0) :
    ∃ cost t, cost ≤ sources.length*(2000*(B+3)^2)+1 ∧
      Executes input tape (factorsCode target sources) cost s t ∧
      Bank t.val (Function.update v target ((sources.map values).prod*v target)) ∧
      Scratch t.val 0 ∧ RationalAccumulator.Frame s.val t.val := by
  induction sources generalizing v s with
  | nil =>
      refine ⟨1,s,by simp,Executes.skip s,?_,hr,?_⟩
      · simpa using hb
      · exact ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ _ => rfl,fun _ _ _ _ _ _ => rfl⟩
  | cons source rest ih =>
      have hsource := hs source (by simp)
      obtain ⟨c,u,hc,eu,ub,ur,uf⟩ := step source target hsource ht ht' input tape v
        (values source) s (hw source (by simp)) hb hr
      have hc' : c ≤ 2000*(B+3)^2 := by
        apply hc.trans
        gcongr
        simp only [bitSum,List.map_cons,List.sum_cons] at hwidth
        omega
      have hwidth' : bitSum rest values+
          (Function.update v target (values source*v target) target).bits.length ≤ B := by
        simp only [Function.update_self]
        have hp := bits_mul_le (values source) (v target)
        simp only [bitSum,List.map_cons,List.sum_cons] at hwidth ⊢
        omega
      have uw : ∀ i ∈ rest,Word u.val i (values i) := by
        intro i hi
        have hi37 := hs i (by simp [hi])
        exact word_of_eq (uf.2.2.2.2.2.1 i (by omega) (Or.inr (by omega))) (hw i (by simp [hi]))
      obtain ⟨d,t,hd,et,tb,tr,tf⟩ := ih (fun i hi => hs i (by simp [hi]))
        _ hwidth' u uw ub ur
      refine ⟨c+d,t,?_,eu.seq et,?_,tr,uf.trans tf⟩
      · simp only [List.length_cons]
        nlinarith
      · simpa only [List.map_cons,List.prod_cons,Function.update_self,
          Function.update_idem,mul_assoc,mul_left_comm] using tb

def code (source target : ℕ) (factors : List ℕ) : Code :=
  .seq (.call (WordTransfer.clone source target)) (factorsCode target factors)

theorem executes (source target : ℕ) (rest : List ℕ)
    (hs : 37 ≤ source) (hrest : ∀ i ∈ rest,37 ≤ i) (ht : 30 ≤ target) (ht' : target ≤ 36)
    (values v : ℕ → ℕ) (B : ℕ) (hwidth : bitSum (source::rest) values ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hw : ∀ i ∈ source::rest,Word s.val i (values i)) (hb : Bank s.val v)
    (hz : v target=0) (hr : Scratch s.val 0) :
    ∃ cost t, cost ≤ (rest.length+1)*(2000*(B+3)^2)+1 ∧
      Executes input tape (code source target rest) cost s t ∧
      Bank t.val (Function.update v target ((rest.map values).prod*values source)) ∧
      Scratch t.val 0 ∧ RationalAccumulator.Frame s.val t.val := by
  obtain ⟨u,eu,ub,ur,uf⟩ := NormalizeCoefficient.clone_external source target hs ht ht'
    input tape v (values source) s hb hr hz (hw source (by simp))
  have uw : ∀ i ∈ rest,Word u.val i (values i) := by
    intro i hi
    have hg := hrest i hi
    exact word_of_eq (uf.2.2.2.2.2.1 i (by omega) (Or.inr (by omega))) (hw i (by simp [hi]))
  obtain ⟨c,t,hc,et,tb,tr,tf⟩ := factors rest target hrest ht ht' values _ B
    (by simp only [Function.update_self]; simpa [bitSum,add_comm] using hwidth)
    input tape u uw ub ur
  refine ⟨(15*(values source).bits.length+17)+c,t,?_,eu.seq et,?_,tr,uf.trans tf⟩
  · have hl : (values source).bits.length ≤ B := by
      simp only [bitSum,List.map_cons,List.sum_cons] at hwidth
      omega
    nlinarith
  · simpa only [Function.update_self,Function.update_idem] using tb

end Maxwell.Cost.PhysicalDecoder.Product
