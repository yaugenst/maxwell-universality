import Maxwell.Continuum.CalibrationMatrixEntryParameters

/-! Fixed scalar arithmetic for the literal forcing R₀f: three free inverse
entries multiply three stored source components. Reciprocal admissibility is
derived from the actual calibration box. -/

namespace Maxwell.Continuum.Calibration.RawFree

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow FreeFiber
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def forcingSource (v : ℕ→Parts) (j : Fin 3) : Parts := v (28+j.val)
def forcingFinish (j : Fin 3) : Control := .step (.binary .mul 12 12 (28+j.val))
  (.step (.binary .add 36 36 12) .done)
def forcingTerm (j : Fin 3) : Control := .step (.literal 24 (j.val:ℚ))
  (indexedFreeControl.andThen (forcingFinish j))

def forcingProtected (k : ℕ) : Prop :=
  k<2 ∨ (13≤k ∧ k≤18) ∨ k=23 ∨ (28≤k ∧ k≤30)

theorem forcingFinish_valid (j : Fin 3) : (forcingFinish j).Valid neighborRegisters := by
  fin_cases j <;> simp [forcingFinish,Control.Valid,Instruction.Valid,neighborRegisters]
theorem forcingFinish_admissible (j : Fin 3) (v : ℕ→Parts) : (forcingFinish j).AdmissibleTrace v := by
  simp [forcingFinish,Control.AdmissibleTrace,Instruction.Admissible]
theorem forcingTerm_valid (j : Fin 3) : (forcingTerm j).Valid neighborRegisters :=
  ⟨by change 24∈Finset.range 41; decide,Control.andThen_valid _ _ _
    (indexedFree_valid.mono stage_subset_neighbors) (forcingFinish_valid j)⟩

theorem forcingTerm_keep (j : Fin 3) (v : ℕ→Parts) (k : ℕ) (hk : forcingProtected k) :
    (forcingTerm j).evaluate v k=v k := by
  unfold forcingProtected at hk
  rw [forcingTerm,Control.evaluate,Control.andThen_evaluate]
  simp (disch := omega) only [forcingFinish,Control.evaluate,Instruction.update,Function.update_of_ne]
  rw [indexedFree_other _ k (by omega)]
  exact Function.update_of_ne (by omega) _ _

theorem forcingFinish_value (j : Fin 3) (v : ℕ→Parts) (hg : Good neighborRegisters v) :
    ((forcingFinish j).evaluate v 36).value=(v 36).value+(v 12).value*(forcingSource v j).value := by
  have hj : 28+j.val∈neighborRegisters := by simp only [neighborRegisters,Finset.mem_range]; omega
  simp only [forcingFinish,Control.evaluate,Instruction.update,BinaryOp.eval,Function.update_self,
    Function.update_of_ne (by decide : (36:ℕ)≠12)]
  rw [Parts.add_value _ _ (hg 36 (by decide)) (Parts.mul_valid (hg 12 (by decide)) (hg _ hj)),Parts.mul_value]
  rfl

theorem forcingTerm_contract (j : Fin 3) (v : ℕ→Parts) (hg : Good neighborRegisters v)
    (ν : Alias) (hν : ∀ k, (coordinates v k).value=(ν k:ℚ))
    (ht : (3:ℝ)≤(v 0).value) (hE : (7:ℝ)≤(v 1).value ∧ ((v 1).value:ℝ)≤8)
    (hr : ∀ k, |((quasiParts v k).value:ℝ)|≤1/16)
    (i : Fin 3) (hi : (v 23).value=(i.val:ℚ)) :
    (forcingTerm j).AdmissibleTrace v ∧
      ((forcingTerm j).evaluate v 36).value=(v 36).value+
        rationalFreeInverseMatrix (v 0).value (v 1).value (fun k => (quasiParts v k).value) ν i j*
          (forcingSource v j).value := by
  let w := Function.update v 24 (Parts.literal (j.val:ℚ))
  have gw : Good neighborRegisters w := hg.update 24 (Parts.literal_valid _)
  have cw : coordinates w=coordinates v := by funext k; fin_cases k <;> rfl
  have qw : quasiParts w=quasiParts v := by funext k; fin_cases k <;> rfl
  obtain ⟨had,hvalue⟩ := indexedFree_contract w (fun k hk => gw k (stage_subset_neighbors hk)) ν
    (by simpa only [cw] using hν) ht hE (by simpa only [qw] using hr) i j hi (by
      simp [w,Parts.literal_value])
  have gf := indexedFreeControl.evaluate_good neighborRegisters
    (indexedFree_valid.mono stage_subset_neighbors) w gw had
  refine ⟨⟨trivial,Control.andThen_admissible _ _ w had (forcingFinish_admissible j _)⟩,?_⟩
  rw [forcingTerm,Control.evaluate,Control.andThen_evaluate]
  change ((forcingFinish j).evaluate (indexedFreeControl.evaluate w) 36).value=_
  rw [forcingFinish_value j _ gf,hvalue,indexedFree_other w 36 (by omega)]
  have source : forcingSource (indexedFreeControl.evaluate w) j=forcingSource v j := by
    rw [forcingSource,indexedFree_other w (28+j.val) (by omega)]
    exact Function.update_of_ne (by omega) _ _
  rw [source,qw]
  rfl

def forcingLoop : List (Fin 3)→Control
  | [] => .done
  | j::rest => (forcingTerm j).andThen (forcingLoop rest)
def forcingControl : Control := .step (.literal 36 0) (forcingLoop [0,1,2])

theorem forcingLoop_valid (js : List (Fin 3)) : (forcingLoop js).Valid neighborRegisters := by
  induction js with
  | nil => trivial
  | cons j rest ih => exact Control.andThen_valid _ _ _ (forcingTerm_valid j) ih

theorem forcingLoop_keep (js : List (Fin 3)) (v : ℕ→Parts) (k : ℕ) (hk : forcingProtected k) :
    (forcingLoop js).evaluate v k=v k := by
  induction js generalizing v with
  | nil => rfl
  | cons j rest ih => rw [forcingLoop,Control.andThen_evaluate,ih,forcingTerm_keep j v k hk]

theorem forcingLoop_contract (js : List (Fin 3)) (v : ℕ→Parts) (hg : Good neighborRegisters v)
    (ν : Alias) (hν : ∀ k, (coordinates v k).value=(ν k:ℚ))
    (ht : (3:ℝ)≤(v 0).value) (hE : (7:ℝ)≤(v 1).value ∧ ((v 1).value:ℝ)≤8)
    (hr : ∀ k, |((quasiParts v k).value:ℝ)|≤1/16)
    (i : Fin 3) (hi : (v 23).value=(i.val:ℚ)) :
    (forcingLoop js).AdmissibleTrace v ∧
      ((forcingLoop js).evaluate v 36).value=(v 36).value+
        (js.map (fun j => rationalFreeInverseMatrix (v 0).value (v 1).value
          (fun k => (quasiParts v k).value) ν i j*(forcingSource v j).value)).sum := by
  induction js generalizing v with
  | nil => simp [forcingLoop,Control.evaluate,Control.AdmissibleTrace]
  | cons j rest ih =>
    obtain ⟨ha,hval⟩ := forcingTerm_contract j v hg ν hν ht hE hr i hi
    let w := (forcingTerm j).evaluate v
    have gw := (forcingTerm j).evaluate_good neighborRegisters (forcingTerm_valid j) v hg ha
    have keep (k : ℕ) (hk : forcingProtected k) : w k=v k := forcingTerm_keep j v k hk
    have cw : coordinates w=coordinates v := by
      funext k
      fin_cases k
      · exact keep 13 (by simp [forcingProtected])
      · exact keep 14 (by simp [forcingProtected])
      · exact keep 15 (by simp [forcingProtected])
    have qw : quasiParts w=quasiParts v := by
      funext k
      fin_cases k
      · exact keep 16 (by simp [forcingProtected])
      · exact keep 17 (by simp [forcingProtected])
      · exact keep 18 (by simp [forcingProtected])
    have fw : forcingSource w=forcingSource v := by
      funext k
      exact keep (28+k.val) (by unfold forcingProtected; omega)
    have h0 := keep 0 (by simp [forcingProtected])
    have h1 := keep 1 (by simp [forcingProtected])
    obtain ⟨hrest,vrest⟩ := ih w gw (by simpa only [cw] using hν)
      (by simpa only [h0] using ht) (by simpa only [h1] using hE)
      (by simpa only [qw] using hr) (by simpa only [keep 23 (by simp [forcingProtected])] using hi)
    refine ⟨Control.andThen_admissible _ _ v ha hrest,?_⟩
    rw [forcingLoop,Control.andThen_evaluate,vrest]
    rw [h0,h1,qw,fw]
    change ((forcingTerm j).evaluate v 36).value+_= _
    rw [hval]
    simp only [List.map_cons,List.sum_cons]
    ring

theorem forcingControl_contract (v : ℕ→Parts) (hg : Good neighborRegisters v)
    (ν : Alias) (hν : ∀ k, (coordinates v k).value=(ν k:ℚ))
    (ht : (3:ℝ)≤(v 0).value) (hE : (7:ℝ)≤(v 1).value ∧ ((v 1).value:ℝ)≤8)
    (hr : ∀ k, |((quasiParts v k).value:ℝ)|≤1/16)
    (i : Fin 3) (hi : (v 23).value=(i.val:ℚ)) :
    forcingControl.AdmissibleTrace v ∧
      (forcingControl.evaluate v 36).value=∑ j,
        rationalFreeInverseMatrix (v 0).value (v 1).value (fun k => (quasiParts v k).value) ν i j*
          (forcingSource v j).value := by
  let w := Function.update v 36 (Parts.literal 0)
  have cw : coordinates w=coordinates v := by funext k; fin_cases k <;> rfl
  have qw : quasiParts w=quasiParts v := by funext k; fin_cases k <;> rfl
  have fw : forcingSource w=forcingSource v := by
    funext k
    exact Function.update_of_ne (by omega) _ _
  obtain ⟨ha,hvalue⟩ := forcingLoop_contract [0,1,2] w (hg.update 36 (Parts.literal_valid 0)) ν
    (by simpa only [cw] using hν) ht hE (by simpa only [qw] using hr) i hi
  refine ⟨⟨trivial,ha⟩,?_⟩
  change ((forcingLoop [0,1,2]).evaluate w 36).value=_
  rw [hvalue,qw,fw]
  simp only [w,Function.update_self,Parts.literal_value,zero_add,
    Function.update_of_ne (by decide : (0:ℕ)≠36),Function.update_of_ne (by decide : (1:ℕ)≠36),
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Fin.sum_univ_three]
  ring

#print axioms forcingControl_contract

end Maxwell.Continuum.Calibration.RawFree
