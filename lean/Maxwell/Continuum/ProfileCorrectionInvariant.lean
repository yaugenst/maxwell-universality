import Maxwell.Continuum.ProfileCorrectionWidths

/-! The correction traversal preserves the computed moments and uses a
linear-width internal descending index. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow
set_option maxHeartbeats 3500000

def correctionWorkingWidth (n B : ℕ) : ℕ := 16*(B+n+2)
def correctionValues {n : ℕ} (a : PartArray.Table n) (v : ℕ→Parts) (k : ℕ) : ℕ→Parts :=
  PartArray.iterate a 1 correctionControl v k
def correctionLoaded {n : ℕ} (a : PartArray.Table n) (v : ℕ→Parts) (k : ℕ) : ℕ→Parts :=
  PartArray.loaded a 1 correctionControl v k

structure CorrectionInvariant (n B k : ℕ) (initial v : ℕ→Parts) : Prop where
  good : Good dftRegisters v
  width : WidthBank dftRegisters (correctionWorkingWidth n B) v
  indexWidth : (v 8).Width (B+2*k)
  indexValue : (v 8).value=(n:ℚ)-k
  constants : ∀i∈correctionConstants,v i=initial i

theorem correctionLoaded_good {n B k : ℕ} {a : PartArray.Table n} {v : ℕ→Parts}
    (h : CorrectionInvariant n B k v (correctionValues a v k)) (ha : ∀i,(a.get i).Valid) :
    Good dftRegisters (correctionLoaded a v k) := h.good.update 1 (a.getD_valid ha _)

theorem correctionLoaded_trace {n B k : ℕ} {a : PartArray.Table n} {v : ℕ→Parts}
    (h : CorrectionInvariant n B k v (correctionValues a v k)) (hk : k<n)
    (hB : 1≤B) (ha : ∀i,(a.get i).Width B)
    (hconst : ∀i∈correctionConstants,(v i).Width B) (h7 : v 7=Parts.literal 1) :
    correctionControl.WidthTrace dftRegisters (correctionWorkingWidth n B) (correctionLoaded a v k) := by
  have fixed (i : ℕ) (hi : i∈correctionConstants) : correctionLoaded a v k i=v i := by
    have hn : i≠1 := by simp only [correctionConstants,Finset.mem_insert,Finset.mem_singleton] at hi;omega
    simpa only [correctionLoaded,PartArray.loaded,correctionValues,Function.update_of_ne hn] using h.constants i hi
  have w1 : (correctionLoaded a v k 1).Width B := by
    simpa only [correctionLoaded,PartArray.loaded,Function.update_self] using a.getD_width B hB ha (n-1-k)
  have hloaded : WidthBank dftRegisters (correctionWorkingWidth n B) (correctionLoaded a v k) :=
    h.width.update 1 ((a.getD_width B hB ha _).mono (by unfold correctionWorkingWidth;omega))
  apply correctionControl_width (correctionLoaded a v k) B (B+2*k) _ hloaded
  · rw [fixed 0 (by decide)];exact hconst 0 (by decide)
  · exact w1
  · rw [fixed 3 (by decide)];exact hconst 3 (by decide)
  · rw [fixed 6 (by decide)];exact hconst 6 (by decide)
  · rw [fixed 7 (by decide),h7];simp [Parts.Width,Parts.literal]
  · simpa only [correctionLoaded,PartArray.loaded,correctionValues,Function.update_of_ne (by decide : (8:ℕ)≠1)] using h.indexWidth
  · unfold correctionWorkingWidth;omega

theorem correction_invariant {n : ℕ} (a : PartArray.Table n) (v : ℕ→Parts) (B : ℕ)
    (hB : 1≤B) (ha : ∀i,(a.get i).Width B) (hav : ∀i,(a.get i).Valid)
    (hg : Good dftRegisters v) (hw : WidthBank dftRegisters (correctionWorkingWidth n B) v)
    (hconst : ∀i∈correctionConstants,(v i).Width B) (h7 : v 7=Parts.literal 1)
    (h8w : (v 8).Width B) (h8v : (v 8).value=n) (k : ℕ) (hk : k≤n) :
    CorrectionInvariant n B k v (correctionValues a v k) := by
  induction k with
  | zero => exact ⟨hg,hw,by simpa [correctionValues,PartArray.iterate] using h8w,by simpa [correctionValues,PartArray.iterate] using h8v,fun _ _ => rfl⟩
  | succ k ih =>
    have hh := ih (by omega)
    have hk' : k<n := by omega
    have hl := correctionLoaded_good hh hav
    have ht := correctionLoaded_trace hh hk' hB ha hconst h7
    have hseven : correctionLoaded a v k 7=Parts.literal 1 := by
      simpa only [correctionLoaded,PartArray.loaded,correctionValues,Function.update_of_ne (by decide : (7:ℕ)≠1)] using
        (hh.constants 7 (by decide)).trans h7
    have hindex : correctionLoaded a v k 8=correctionValues a v k 8 := by
      simp only [correctionLoaded,PartArray.loaded,correctionValues,Function.update_of_ne (by decide : (8:ℕ)≠1)]
    refine ⟨correctionControl.evaluate_good _ correctionControl_valid _ hl
      (correctionControl_admissible _),ht.result,?_,?_,?_⟩
    · change (correctionControl.evaluate (correctionLoaded a v k) 8).Width _
      rw [correctionControl_index,hseven,hindex]
      have w1 : (Parts.literal 1).Width 1 := by simp [Parts.Width,Parts.literal]
      convert hh.indexWidth.sub w1 using 1
    · change (correctionControl.evaluate (correctionLoaded a v k) 8).value=_
      rw [correctionControl_index,Parts.sub_value _ _ (hl 8 (by decide)) (hl 7 (by decide)),
        hindex,hh.indexValue,hseven,Parts.literal_value]
      push_cast
      ring
    · intro i hi
      change correctionControl.evaluate (correctionLoaded a v k) i=v i
      rw [correctionControl_const _ _ hi]
      have hn : i≠1 := by simp only [correctionConstants,Finset.mem_insert,Finset.mem_singleton] at hi;omega
      simpa only [correctionLoaded,PartArray.loaded,correctionValues,Function.update_of_ne hn] using hh.constants i hi

theorem correctionValues_output {n : ℕ} (a : PartArray.Table n) (v : ℕ→Parts) (B k : ℕ)
    (hk : k<n) (h : CorrectionInvariant n B k v (correctionValues a v k))
    (ha : ∀i,(a.get i).Valid) (h7 : v 7=Parts.literal 1) :
    (correctionValues a v (k+1) 1).value=
      correctedValue (v 0).value (v 3).value (v 6).value (a.getD (n-1-k)).value (n-1-k) := by
  have hl := correctionLoaded_good h ha
  have fixed (i : ℕ) (hi : i∈correctionConstants) : correctionLoaded a v k i=v i := by
    have hn : i≠1 := by simp only [correctionConstants,Finset.mem_insert,Finset.mem_singleton] at hi;omega
    simpa only [correctionLoaded,PartArray.loaded,correctionValues,Function.update_of_ne hn] using h.constants i hi
  have index : (correctionLoaded a v k 8).value=((n-1-k:ℕ):ℚ)+1 := by
    have hv : (correctionLoaded a v k 8).value=(n:ℚ)-k := by
      simpa only [correctionLoaded,PartArray.loaded,correctionValues,Function.update_of_ne (by decide : (8:ℕ)≠1)] using h.indexValue
    rw [hv]
    have hn : n=k+((n-1-k)+1) := by omega
    have hnq : (n:ℚ)=(k:ℚ)+(((n-1-k:ℕ):ℚ)+1) := by exact_mod_cast hn
    linarith
  have he := correctionControl_value (correctionLoaded a v k) hl (n-1-k)
    (by rw [fixed 7 (by decide),h7,Parts.literal_value]) index
  change (correctionControl.evaluate (correctionLoaded a v k) 1).value=_
  rw [he,fixed 0 (by decide),fixed 3 (by decide),fixed 6 (by decide)]
  rfl

#print axioms correction_invariant
#print axioms correctionValues_output
end Maxwell.Continuum.Profile.Runtime
