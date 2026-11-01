import Maxwell.Cost.Structured.Footprint

/-! One finite syntax check certifies preservation of an interval of tapes,
without repeatedly unfolding the same large program for every register. -/
namespace Maxwell.Cost

def BitRAMInstruction.outsideTapes (lo hi : ℕ) : BitRAMInstruction→Bool
  | .writeTape target _ | .eraseTape target | .tapeLeft target | .tapeRight target => decide (target<lo ∨ hi≤target)
  | _ => true

def BitRAM.outsideTapes (lo hi : ℕ) (body : BitRAM) : Bool := body.code.all (BitRAMInstruction.outsideTapes lo hi)

theorem BitRAM.outsideTapes_protects {lo hi i : ℕ} {body : BitRAM}
    (h : body.outsideTapes lo hi=true) (hlo : lo ≤ i) (hhi : i<hi) : body.protectsTape i=true := by
  apply List.all_eq_true.mpr
  intro a ha
  have hh := List.all_eq_true.mp h a ha
  cases a <;> simp_all [BitRAMInstruction.outsideTapes,BitRAMInstruction.protectsTape]
  all_goals omega

namespace Structured

def Code.outsideTapes (lo hi : ℕ) : Code→Bool
  | .skip => true
  | .call body => body.outsideTapes lo hi
  | .seq a b => a.outsideTapes lo hi && b.outsideTapes lo hi
  | .branch _ a b => a.outsideTapes lo hi && b.outsideTapes lo hi
  | .loop _ body => body.outsideTapes lo hi

theorem Code.outsideTapes_protects {lo hi i : ℕ} {code : Code}
    (h : code.outsideTapes lo hi=true) (hlo : lo ≤ i) (hhi : i<hi) : code.protectsTape i=true := by
  induction code with
  | skip => rfl
  | call body => exact body.outsideTapes_protects h hlo hhi
  | seq a b ia ib =>
    simp only [Code.outsideTapes,Bool.and_eq_true] at h
    simp only [Code.protectsTape, ia h.1, ib h.2, Bool.and_self]
  | branch _ a b ia ib =>
    simp only [Code.outsideTapes,Bool.and_eq_true] at h
    simp only [Code.protectsTape, ia h.1, ib h.2, Bool.and_self]
  | loop _ body ih => exact ih h

theorem Executes.outsideTapes {input : List Bool} {tape : ℕ→Bool} {code : Code}
    {cost lo hi : ℕ} {s t : Store} (e : Executes input tape code cost s t)
    (h : code.outsideTapes lo hi=true) (i : ℕ) (hlo : lo ≤ i) (hhi : i<hi) :
    t.val.tapes i=s.val.tapes i := e.protectsTape i (Code.outsideTapes_protects h hlo hhi)

#print axioms Code.outsideTapes_protects
end Structured
end Maxwell.Cost
