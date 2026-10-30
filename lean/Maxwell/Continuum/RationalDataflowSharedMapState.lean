import Maxwell.Continuum.RationalDataflowArrayOutputFrame
import Maxwell.Continuum.RationalDataflowSharedConversion
import Maxwell.Continuum.RationalDataflowArrayProgram

/-! Exact contents and raw-width invariants of the shared-denominator table pass. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def sharedSlots : Finset ℕ := {0,1,2}
def sharedWidth (n W : ℕ) : ℕ := (n+2)*(W+1)+1

def sharedState {n : ℕ} (a : Table n) (v : ℕ→Parts) : ℕ→(ℕ→Parts) :=
  programIterate a 1 (SharedConversion.convertStep 0 1 2) v

def sharedLoaded {n : ℕ} (a : Table n) (v : ℕ→Parts) (k : ℕ) : ℕ→Parts :=
  programLoaded a 1 (SharedConversion.convertStep 0 1 2) v k

theorem sharedState_denominator {n : ℕ} (a : Table n) (v : ℕ→Parts) (k : ℕ) :
    sharedState a v k 0=v 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [sharedState,programIterate,SharedConversion.convertStep,
      SharedConversion.scaleStep,SharedConversion.quotientStep,Function.update_of_ne (by decide : (0:ℕ)≠1),
      Function.update_of_ne (by decide : (0:ℕ)≠2)] using ih

theorem sharedState_entry {n : ℕ} (a : Table n) (v : ℕ→Parts)
    (hD : (v 0).positive=SharedTable.denominator a.get) (k : ℕ) (hk : k<n) :
    sharedState a v (k+1) 1=SharedTable.integerParts a.get ⟨n-1-k,by omega⟩ := by
  apply SharedConversion.convert_entry_integerParts a.get ⟨n-1-k,by omega⟩ 0 1 2 (by decide)
  · simp only [Function.update_of_ne (by decide : (0:ℕ)≠1)]
    change (sharedState a v k 0).positive=SharedTable.denominator a.get
    rw [sharedState_denominator]
    exact hD
  · simp only [Function.update_self,Table.getD,dite_eq_left (show n-1-k<n by omega)]

theorem sharedState_width {n : ℕ} (a : Table n) (v : ℕ→Parts) (W : ℕ) (hW : 1≤W)
    (ha : ∀ i, (a.get i).Width W) (hv : WidthBank sharedSlots (sharedWidth n W) v)
    (hD : (v 0).positive=SharedTable.denominator a.get) (k : ℕ) (hk : k≤n) :
    WidthBank sharedSlots (sharedWidth n W) (sharedState a v k) := by
  have hw : W≤sharedWidth n W := by unfold sharedWidth; nlinarith
  have hib (i : Fin n) : (SharedTable.integerParts a.get i).Width (sharedWidth n W) := by
    apply (SharedTable.integerParts_width a.get W ha i).mono
    simp only [Fintype.card_fin]
    unfold sharedWidth
    nlinarith
  induction k with
  | zero => exact hv
  | succ k ih =>
    have hk' : k<n := by omega
    have prior := ih (by omega)
    have loaded := prior.update 1 ((a.getD_width W hW ha (n-1-k)).mono hw)
    have quotient := SharedConversion.quotientStep_width sharedSlots 0 1 2 (by decide) (by decide)
      _ (sharedWidth n W) loaded
    have herr := sharedState_entry a v hD k hk'
    have current := WidthBank.update quotient 1 (hib ⟨n-1-k,by omega⟩)
    convert current using 1
    funext i
    by_cases hi : i=1
    · subst i
      simpa only [Function.update_self] using herr
    · simp only [sharedState,programIterate,SharedConversion.convertStep,
        SharedConversion.scaleStep,Function.update_of_ne hi]

theorem sharedLoaded_width {n : ℕ} (a : Table n) (v : ℕ→Parts) (W : ℕ) (hW : 1≤W)
    (ha : ∀ i, (a.get i).Width W) (hv : WidthBank sharedSlots (sharedWidth n W) v)
    (hD : (v 0).positive=SharedTable.denominator a.get) (k : ℕ) (hk : k<n) :
    WidthBank sharedSlots (sharedWidth n W) (sharedLoaded a v k) :=
  (sharedState_width a v W hW ha hv hD k hk.le).update 1
    ((a.getD_width W hW ha _).mono (by unfold sharedWidth; nlinarith))

def filledWords {n : ℕ} (width : ℕ) (original : Vector (List Bool) n)
    (value : Fin n→ℕ) (remaining : ℕ) : Vector (List Bool) n :=
  Vector.ofFn (fun i => if remaining ≤ i.val then FixedWidth.bits width (value i).bits else original.get i)

theorem filledWords_get {n : ℕ} (width : ℕ) (original : Vector (List Bool) n)
    (value : Fin n→ℕ) (remaining : ℕ) (i : Fin n) :
    (filledWords width original value remaining).get i=
      if remaining ≤ i.val then FixedWidth.bits width (value i).bits else original.get i := by
  simp [filledWords,Vector.get,Fin.cast]

theorem filledWords_initial {n : ℕ} (width : ℕ) (original : Vector (List Bool) n)
    (value : Fin n→ℕ) : filledWords width original value n=original := by
  apply Vector.ext
  intro i hi
  have h := filledWords_get width original value n ⟨i,hi⟩
  simpa [Vector.get,Fin.cast,show ¬n ≤ i by omega] using h

theorem filledWords_step {n : ℕ} (width : ℕ) (original : Vector (List Bool) n)
    (value : Fin n→ℕ) (r : ℕ) (hr : r<n) :
    (filledWords width original value (r+1)).set r (FixedWidth.bits width (value ⟨r,hr⟩).bits)=
      filledWords width original value r := by
  apply Vector.ext
  intro i hi
  change (((filledWords width original value (r+1)).set r
    (FixedWidth.bits width (value ⟨r,hr⟩).bits)).get ⟨i,hi⟩)=_
  rw [show (((filledWords width original value (r+1)).set r
    (FixedWidth.bits width (value ⟨r,hr⟩).bits)).get ⟨i,hi⟩)=
    (if r=i then FixedWidth.bits width (value ⟨r,hr⟩).bits else
      (filledWords width original value (r+1)).get ⟨i,hi⟩) by simp [Vector.get,Fin.cast,Array.getElem_set]]
  rw [filledWords_get]
  change _=(filledWords width original value r).get ⟨i,hi⟩
  rw [filledWords_get]
  by_cases hir : r=i
  · subst i
    simp
  · have heq : r+1 ≤ i ↔ r ≤ i := by omega
    simp [hir,heq]

def Table.filled {n : ℕ} (b : Table n) (value : Fin n→Parts) (remaining : ℕ) : Table n :=
  { b with
    positive := filledWords (addressValue b.width) b.positive (fun i => (value i).positive) remaining
    negative := filledWords (addressValue b.width) b.negative (fun i => (value i).negative) remaining
    denominator := filledWords (addressValue b.width) b.denominator (fun i => (value i).denominator) remaining }

theorem Table.filled_initial {n : ℕ} (b : Table n) (value : Fin n→Parts) : b.filled value n=b := by
  simp only [Table.filled,filledWords_initial]

theorem Table.filled_step {n : ℕ} (b : Table n) (value : Fin n→Parts) (r : ℕ) (hr : r<n) :
    (b.filled value (r+1)).set ⟨r,hr⟩ (value ⟨r,hr⟩)=b.filled value r := by
  simp only [Table.filled,Table.set,filledWords_step]

theorem Table.filled_get {n : ℕ} (b : Table n) (value : Fin n→Parts)
    (hfit : ∀ i, (value i).Width (addressValue b.width)) (i : Fin n) :
    (b.filled value 0).get i=value i := by
  have hp := FixedWidth.bits_value (addressValue b.width) (value i).positive.bits (hfit i).1
  have hn := FixedWidth.bits_value (addressValue b.width) (value i).negative.bits (hfit i).2.1
  have hd := FixedWidth.bits_value (addressValue b.width) (value i).denominator.bits (hfit i).2.2
  simp only [Table.filled,Table.get,filledWords_get,Nat.zero_le,ite_true,hp,hn,hd,addressValue_bits]

#print axioms sharedState_width
#print axioms Table.filled_get
end Maxwell.Continuum.RationalDataflow.PartArray
