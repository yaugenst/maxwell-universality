import Maxwell.Continuum.CalibrationForcingExecution

/-! All three polarization components are computed from one alias's three
stored source values. The fixed program stores them in registers 37,38,39. -/

namespace Maxwell.Continuum.Calibration.RawFree

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow FreeFiber
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def forcingStable (k : ℕ) : Prop := (k<2 ∨ (13≤k ∧ k≤18) ∨ 28≤k) ∧ k≠36

theorem forcingTerm_keep_all (j : Fin 3) (v : ℕ→Parts) (k : ℕ) (hk : forcingStable k) :
    (forcingTerm j).evaluate v k=v k := by
  unfold forcingStable at hk
  rw [forcingTerm,Control.evaluate,Control.andThen_evaluate]
  simp (disch := omega) only [forcingFinish,Control.evaluate,Instruction.update,Function.update_of_ne]
  rw [indexedFree_other _ k (by omega)]
  exact Function.update_of_ne (by omega) _ _

theorem forcingLoop_keep_all (js : List (Fin 3)) (v : ℕ→Parts) (k : ℕ) (hk : forcingStable k) :
    (forcingLoop js).evaluate v k=v k := by
  induction js generalizing v with
  | nil => rfl
  | cons j rest ih => rw [forcingLoop,Control.andThen_evaluate,ih,forcingTerm_keep_all j v k hk]

theorem forcingControl_keep (v : ℕ→Parts) (k : ℕ) (hk : forcingStable k) :
    forcingControl.evaluate v k=v k := by
  rw [forcingControl,Control.evaluate,forcingLoop_keep_all _ _ k hk]
  exact Function.update_of_ne hk.2 _ _

def forcingCoefficient (v : ℕ→Parts) (ν : Alias) (i : Fin 3) : ℚ := ∑ j,
  rationalFreeInverseMatrix (v 0).value (v 1).value (fun k => (quasiParts v k).value) ν i j*
    (forcingSource v j).value

def forcingVectorTerm (i : Fin 3) : Control := .step (.literal 23 (i.val:ℚ))
  (forcingControl.andThen (.step (.binary .mul (37+i.val) 36 40) .done))

theorem forcingVectorTerm_valid (i : Fin 3) : (forcingVectorTerm i).Valid neighborRegisters := by
  refine ⟨by change 23∈Finset.range 41; decide,Control.andThen_valid _ _ _ forcingControl_valid ?_⟩
  fin_cases i <;> simp [Control.Valid,Instruction.Valid,neighborRegisters]

theorem forcingVectorTerm_keep (i : Fin 3) (v : ℕ→Parts) (k : ℕ)
    (hk : forcingStable k) (hi : k≠37+i.val) : (forcingVectorTerm i).evaluate v k=v k := by
  rw [forcingVectorTerm,Control.evaluate,Control.andThen_evaluate]
  simp only [Control.evaluate,Instruction.update,Function.update_of_ne hi]
  rw [forcingControl_keep _ k hk]
  exact Function.update_of_ne (by unfold forcingStable at hk; omega) _ _

theorem forcingVectorTerm_coefficient (i j : Fin 3) (v : ℕ→Parts) (ν : Alias) :
    forcingCoefficient ((forcingVectorTerm i).evaluate v) ν j=forcingCoefficient v ν j := by
  have h0 := forcingVectorTerm_keep i v 0 (by simp [forcingStable]) (by omega)
  have h1 := forcingVectorTerm_keep i v 1 (by simp [forcingStable]) (by omega)
  have hq : quasiParts ((forcingVectorTerm i).evaluate v)=quasiParts v := by
    funext k
    fin_cases k
    · exact forcingVectorTerm_keep i v 16 (by simp [forcingStable]) (by omega)
    · exact forcingVectorTerm_keep i v 17 (by simp [forcingStable]) (by omega)
    · exact forcingVectorTerm_keep i v 18 (by simp [forcingStable]) (by omega)
  have hf : forcingSource ((forcingVectorTerm i).evaluate v)=forcingSource v := by
    funext k
    exact forcingVectorTerm_keep i v (28+k.val) (by unfold forcingStable; omega) (by omega)
  simp only [forcingCoefficient,h0,h1,hq,hf]

theorem forcingVectorTerm_contract (i : Fin 3) (v : ℕ→Parts) (hg : Good neighborRegisters v)
    (ν : Alias) (hν : ∀ k, (coordinates v k).value=(ν k:ℚ))
    (ht : (3:ℝ)≤(v 0).value) (hE : (7:ℝ)≤(v 1).value ∧ ((v 1).value:ℝ)≤8)
    (hr : ∀ k, |((quasiParts v k).value:ℝ)|≤1/16) (hone : (v 40).value=1) :
    (forcingVectorTerm i).AdmissibleTrace v ∧
      ((forcingVectorTerm i).evaluate v (37+i.val)).value=forcingCoefficient v ν i := by
  let w := Function.update v 23 (Parts.literal (i.val:ℚ))
  have cw : coordinates w=coordinates v := by funext k; fin_cases k <;> rfl
  have qw : quasiParts w=quasiParts v := by funext k; fin_cases k <;> rfl
  have fw : forcingSource w=forcingSource v := by
    funext k
    exact Function.update_of_ne (by omega) _ _
  obtain ⟨ha,hvalue⟩ := forcingControl_contract w (hg.update 23 (Parts.literal_valid _)) ν
    (by simpa only [cw] using hν) ht hE (by simpa only [qw] using hr) i (by simp [w,Parts.literal_value])
  refine ⟨⟨trivial,Control.andThen_admissible _ _ w ha ⟨trivial,trivial⟩⟩,?_⟩
  rw [forcingVectorTerm,Control.evaluate,Control.andThen_evaluate]
  simp only [Control.evaluate,Instruction.update,BinaryOp.eval,Function.update_self]
  change (Parts.mul (forcingControl.evaluate w 36) (forcingControl.evaluate w 40)).value=_
  rw [Parts.mul_value,forcingControl_keep w 40 (by simp [forcingStable])]
  change (forcingControl.evaluate w 36).value*(v 40).value=_
  rw [hone,mul_one,hvalue,qw,fw]
  rfl

def forcingVectorLoop : List (Fin 3)→Control
  | [] => .done
  | i::rest => (forcingVectorTerm i).andThen (forcingVectorLoop rest)
abbrev forcingVectorControl : Control := .step (.literal 40 1) (forcingVectorLoop [0,1,2])

theorem forcingVectorLoop_valid (js : List (Fin 3)) : (forcingVectorLoop js).Valid neighborRegisters := by
  induction js with
  | nil => trivial
  | cons i rest ih => exact Control.andThen_valid _ _ _ (forcingVectorTerm_valid i) ih

theorem forcingVectorLoop_keep (js : List (Fin 3)) (v : ℕ→Parts) (k : ℕ)
    (hk : forcingStable k) (hjs : ∀ i∈js, k≠37+i.val) :
    (forcingVectorLoop js).evaluate v k=v k := by
  induction js generalizing v with
  | nil => rfl
  | cons i rest ih =>
    rw [forcingVectorLoop,Control.andThen_evaluate,ih _ (fun j hj => hjs j (by simp [hj])),
      forcingVectorTerm_keep i v k hk (hjs i (by simp))]

theorem forcingVectorLoop_contract (js : List (Fin 3)) (v : ℕ→Parts) (hg : Good neighborRegisters v)
    (ν : Alias) (hν : ∀ k, (coordinates v k).value=(ν k:ℚ))
    (ht : (3:ℝ)≤(v 0).value) (hE : (7:ℝ)≤(v 1).value ∧ ((v 1).value:ℝ)≤8)
    (hr : ∀ k, |((quasiParts v k).value:ℝ)|≤1/16) (hone : (v 40).value=1) :
    (forcingVectorLoop js).AdmissibleTrace v ∧ ∀ i∈js,
      ((forcingVectorLoop js).evaluate v (37+i.val)).value=forcingCoefficient v ν i := by
  induction js generalizing v with
  | nil => exact ⟨trivial,by simp⟩
  | cons j rest ih =>
    obtain ⟨ha,hvalue⟩ := forcingVectorTerm_contract j v hg ν hν ht hE hr hone
    let w := (forcingVectorTerm j).evaluate v
    have gw := (forcingVectorTerm j).evaluate_good neighborRegisters (forcingVectorTerm_valid j) v hg ha
    have keep (k : ℕ) (hk : forcingStable k) (hj : k≠37+j.val) : w k=v k :=
      forcingVectorTerm_keep j v k hk hj
    have cw : coordinates w=coordinates v := by
      funext k
      fin_cases k
      · exact keep 13 (by simp [forcingStable]) (by omega)
      · exact keep 14 (by simp [forcingStable]) (by omega)
      · exact keep 15 (by simp [forcingStable]) (by omega)
    have qw : quasiParts w=quasiParts v := by
      funext k
      fin_cases k
      · exact keep 16 (by simp [forcingStable]) (by omega)
      · exact keep 17 (by simp [forcingStable]) (by omega)
      · exact keep 18 (by simp [forcingStable]) (by omega)
    have h0 := keep 0 (by simp [forcingStable]) (by omega)
    have h1 := keep 1 (by simp [forcingStable]) (by omega)
    have h40 := keep 40 (by simp [forcingStable]) (by omega)
    obtain ⟨had,hrest⟩ := ih w gw (by simpa only [cw] using hν)
      (by simpa only [h0] using ht) (by simpa only [h1] using hE)
      (by simpa only [qw] using hr) (by simpa only [h40] using hone)
    refine ⟨Control.andThen_admissible _ _ v ha had,?_⟩
    intro i hi
    rw [forcingVectorLoop,Control.andThen_evaluate]
    change ((forcingVectorLoop rest).evaluate w (37+i.val)).value=_
    by_cases hir : i∈rest
    · rw [hrest i hir]
      exact forcingVectorTerm_coefficient j i v ν
    · have heq : i=j := by simpa only [List.mem_cons,hir,or_false] using hi
      subst i
      rw [forcingVectorLoop_keep rest w (37+j.val) (by unfold forcingStable; omega)]
      · exact hvalue
      · intro i hi heq
        apply hir
        have eq : j=i := Fin.ext (by omega)
        simpa only [eq] using hi

theorem forcingVectorInitialized_contract (js : List (Fin 3)) (v : ℕ→Parts) (hg : Good neighborRegisters v)
    (ν : Alias) (hν : ∀ k, (coordinates v k).value=(ν k:ℚ))
    (ht : (3:ℝ)≤(v 0).value) (hE : (7:ℝ)≤(v 1).value ∧ ((v 1).value:ℝ)≤8)
    (hr : ∀ k, |((quasiParts v k).value:ℝ)|≤1/16) :
    (Control.step (.literal 40 1) (forcingVectorLoop js)).AdmissibleTrace v ∧ ∀ i∈js,
      ((Control.step (.literal 40 1) (forcingVectorLoop js)).evaluate v (37+i.val)).value=
        forcingCoefficient v ν i := by
  let w := Function.update v 40 (Parts.literal 1)
  have cw : coordinates w=coordinates v := by funext k; fin_cases k <;> rfl
  have qw : quasiParts w=quasiParts v := by funext k; fin_cases k <;> rfl
  have fw : forcingSource w=forcingSource v := by
    funext k
    exact Function.update_of_ne (by omega) _ _
  obtain ⟨ha,hvalue⟩ := forcingVectorLoop_contract js w (hg.update 40 (Parts.literal_valid 1)) ν
    (by simpa only [cw] using hν) ht hE (by simpa only [qw] using hr)
    (by simp [w,Parts.literal_value])
  refine ⟨⟨trivial,ha⟩,?_⟩
  intro i hi
  change ((forcingVectorLoop js).evaluate w (37+i.val)).value=_
  have hv := hvalue i hi
  have hc : forcingCoefficient w ν i=forcingCoefficient v ν i := by
    simp only [forcingCoefficient,qw,fw]
    rfl
  exact hv.trans hc

theorem forcingVectorControl_contract (v : ℕ→Parts) (hg : Good neighborRegisters v)
    (ν : Alias) (hν : ∀ k, (coordinates v k).value=(ν k:ℚ))
    (ht : (3:ℝ)≤(v 0).value) (hE : (7:ℝ)≤(v 1).value ∧ ((v 1).value:ℝ)≤8)
    (hr : ∀ k, |((quasiParts v k).value:ℝ)|≤1/16) :
    forcingVectorControl.AdmissibleTrace v ∧ ∀ i : Fin 3,
      (forcingVectorControl.evaluate v (37+i.val)).value=forcingCoefficient v ν i := by
  have h := forcingVectorInitialized_contract [0,1,2] v hg ν hν ht hE hr
  exact ⟨h.1,fun i => h.2 i (by fin_cases i <;> simp)⟩

#print axioms forcingVectorControl_contract

end Maxwell.Continuum.Calibration.RawFree
