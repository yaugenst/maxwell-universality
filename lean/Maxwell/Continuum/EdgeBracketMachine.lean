import Maxwell.Continuum.EdgeBracketInitial

/-! Actual initialized, midpoint, and branch-update programs for the continuum
edge bracket. The sign is read from register31, produced by the Schur circuit. -/
namespace Maxwell.Continuum.Calibration.EdgeBracketMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Certificate RationalDataflow

def Represents (v : ℕ→ℕ) (I : Interval) : Prop :=
  Denominators v ∧ (words v).lo=I.lo ∧ (words v).hi=I.hi
def midpointCode : Code := SignedBracket.midpointCode base
def stepCode : Code := SignedBracket.stepCode base 31
def midpointResult (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values (SignedBracket.midpointPlan base) v
def stepResult (negative : Bool) (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values (SignedBracket.stepPlan base negative) v

theorem initial_represents : Represents (initial edgeInitial) edgeInitial := by
  refine ⟨initial_denominators _,?_⟩
  rw [initial_words]
  exact EdgeWords.ofInterval_endpoints _

theorem midpoint_represents (v : ℕ→ℕ) (I : Interval) (h : Represents v I) :
    Represents (midpointResult v) I ∧ (parts (midpointResult v) 2302).value=I.midpoint := by
  refine ⟨⟨midpoint_denominators v h.1,?_,?_⟩,?_⟩
  · simpa only [midpointResult,midpoint_words] using h.2.1
  · simpa only [midpointResult,midpoint_words] using h.2.2
  · rw [midpointResult,midpoint_value,EdgeWords.midpoint_eq,h.2.1,h.2.2]
    rfl

theorem step_represents (v : ℕ→ℕ) (I : Interval) (h : Represents v I) (negative : Bool) :
    Represents (stepResult negative v) (edgeStep I negative) := by
  refine ⟨step_denominators v negative h.1,?_⟩
  simp only [stepResult,step_words]
  exact EdgeWords.step_endpoints (words v) I h.1.1 h.2.1 h.2.2 negative

theorem midpoint_executes (v : ℕ→ℕ) (I : Interval) (representation : Represents v I)
    (B : ℕ) (hB : 7≤B) (width : ∀i∈SignedBracket.ids base,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank (SignedBracket.ids base) v s.val) (scratch : NatAssign.Scratch s.val) :
    ∃steps t,Executes input tape midpointCode steps s t ∧ steps≤SignedBracket.midpointCost B ∧
      NatAssign.Bank (SignedBracket.ids base) (midpointResult v) t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈SignedBracket.ids base,(midpointResult v i).bits.length≤B+7) ∧
      Represents (midpointResult v) I ∧
      Cells {2300,2301,2302} (parts (midpointResult v)) t.val ∧
      (parts (midpointResult v) 2302).value=I.midpoint ∧
      BinaryPrecision.Frame ({0,1,2,3}∪SignedBracket.ids base) s.val t.val := by
  obtain ⟨c,t,e,charge,stored,blank,words,frame⟩:=SignedBracket.midpoint_executes base B
    (by decide) hB v width input tape s bank scratch
  have meaning:=midpoint_represents v I representation
  exact ⟨c,t,e,charge,stored,blank,words,meaning.1,bank_cells _ _ stored,meaning.2,frame⟩

theorem step_executes (v : ℕ→ℕ) (I : Interval) (representation : Represents v I)
    (B : ℕ) (hB : 7≤B) (width : ∀i∈SignedBracket.ids base,(v i).bits.length≤B)
    (negative : Bool) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank (SignedBracket.ids base) v s.val) (scratch : NatAssign.Scratch s.val)
    (decision : s.val.registers 31=negative) :
    ∃steps t,Executes input tape stepCode steps s t ∧ steps≤SignedBracket.stepCost B ∧
      NatAssign.Bank (SignedBracket.ids base) (stepResult negative v) t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈SignedBracket.ids base,(stepResult negative v i).bits.length≤B+7) ∧
      Represents (stepResult negative v) (edgeStep I negative) ∧
      Cells {2300,2301,2302} (parts (stepResult negative v)) t.val ∧
      BinaryPrecision.Frame ({0,1,2,3}∪SignedBracket.ids base) s.val t.val := by
  obtain ⟨c,t,e,charge,stored,blank,words,frame⟩:=SignedBracket.step_executes base 31 B
    (by decide) hB negative v width input tape s bank scratch decision
  exact ⟨c,t,e,charge,stored,blank,words,step_represents v I representation negative,
    bank_cells _ _ stored,frame⟩

#print axioms midpoint_executes
#print axioms step_executes
end Maxwell.Continuum.Calibration.EdgeBracketMachine
