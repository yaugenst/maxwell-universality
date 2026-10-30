import Maxwell.Continuum.RationalDataflowTrace

/-! Additive word growth for unreduced integer channels. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost

theorem Parts.Width.add_integer {x y : Parts} {B : ℕ} (hx : x.Width B)
    (hy : y.Width B) (hdx : x.denominator=1) (hdy : y.denominator=1) :
    (x.add y).Width (B+1) := by
  have hp := RationalAccumulator.bits_add_le x.positive y.positive
  have hn := RationalAccumulator.bits_add_le x.negative y.negative
  simp only [Parts.Width,Parts.add,hdx,hdy,Nat.mul_one]
  exact ⟨hp.trans (Nat.add_le_add_right (max_le hx.1 hy.1) 1),
    hn.trans (Nat.add_le_add_right (max_le hx.2.1 hy.2.1) 1),by simp⟩

def IntegerBank (S : Finset ℕ) (v : ℕ→Parts) : Prop := ∀ i∈S,(v i).denominator=1

theorem IntegerBank.update {S : Finset ℕ} {v : ℕ→Parts} (hv : IntegerBank S v)
    (target : ℕ) {x : Parts} (hx : x.denominator=1) : IntegerBank S (Function.update v target x) := by
  intro i hi
  by_cases he : i=target
  · subst i;simpa only [Function.update_self] using hx
  · simpa only [Function.update_of_ne he] using hv i hi

theorem IntegerBank.good {S : Finset ℕ} {v : ℕ→Parts} (hv : IntegerBank S v) : Good S v := by
  intro i hi
  simp only [Parts.Valid,hv i hi]
  exact Nat.zero_lt_one

theorem addInstruction_integer (S : Finset ℕ) (target left right : ℕ)
    (hl : left∈S) (hr : right∈S) (v : ℕ→Parts) (hv : IntegerBank S v) :
    IntegerBank S ((Instruction.binary .add target left right).update v) := by
  apply hv.update
  simp only [BinaryOp.eval,Parts.add,hv left hl,hv right hr,Nat.mul_one]

theorem addInstruction_width (S : Finset ℕ) (target left right : ℕ)
    (hl : left∈S) (hr : right∈S) (v : ℕ→Parts) (B : ℕ)
    (hw : WidthBank S B v) (hv : IntegerBank S v) :
    WidthBank S (B+1) ((Instruction.binary .add target left right).update v) :=
  (hw.mono (Nat.le_succ B)).update target
    ((hw left hl).add_integer (hw right hr) (hv left hl) (hv right hr))

theorem additions_trace (S : Finset ℕ) (ins : List Instruction)
    (hi : ∀a∈ins,∃t l r,a=Instruction.binary .add t l r ∧ l∈S ∧ r∈S)
    (v : ℕ→Parts) (B : ℕ) (hv : IntegerBank S v) (hw : WidthBank S B v) :
    IntegerBank S (evaluate ins v) ∧ WidthBank S (B+ins.length) (evaluate ins v) ∧
      WidthTrace S (B+ins.length) ins v := by
  induction ins generalizing v B with
  | nil => exact ⟨hv,by simpa [evaluate] using hw,by simpa [WidthTrace] using hw⟩
  | cons a rest ih =>
    obtain ⟨t,l,r,rfl,hl,hr⟩ := hi a (by simp)
    have hv1 := addInstruction_integer S t l r hl hr v hv
    have hw1 := addInstruction_width S t l r hl hr v B hw hv
    obtain ⟨hg,hn,ht⟩ := ih (fun a ha => hi a (by simp [ha])) _ (B+1) hv1 hw1
    have he : B+1+rest.length=B+(Instruction.binary .add t l r::rest).length := by simp;omega
    rw [he] at hn ht
    exact ⟨hg,hn,hw.mono (by omega),trivial,ht⟩

#print axioms Parts.Width.add_integer
#print axioms additions_trace
end Maxwell.Continuum.RationalDataflow
