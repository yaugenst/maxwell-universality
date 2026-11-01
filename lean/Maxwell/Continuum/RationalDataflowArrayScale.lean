import Maxwell.Continuum.RationalDataflowArrayMap
import Maxwell.Continuum.RationalDataflowArraySum

/-! A charged array traversal multiplies each raw entry by one retained raw
scalar. The width bound is independent of the number of entries. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def scaleBody (scalar : ℕ) : Control := .step (.binary .mul 1 1 scalar) .done

theorem scale_retained {n : ℕ} (a : Table n) (scalar : ℕ) (hne : scalar≠1)
    (v : ℕ→Parts) (k : ℕ) : iterate a 1 (scaleBody scalar) v k scalar=v scalar := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [iterate,scaleBody,Control.evaluate,Instruction.update,Function.update_of_ne hne]
      using ih

theorem scale_result {n : ℕ} (a : Table n) (scalar : ℕ) (hne : scalar≠1)
    (v : ℕ→Parts) (k : ℕ) :
    iterate a 1 (scaleBody scalar) v (k+1) 1=(a.getD (n-1-k)).mul (v scalar) := by
  have retained:=scale_retained a scalar hne v k
  simp only [scaleBody] at retained
  simp only [iterate,scaleBody,Control.evaluate,Instruction.update,BinaryOp.eval,
    Function.update_self,Function.update_of_ne hne,retained]

theorem scale_iterate_good {n : ℕ} (a : Table n) (S : Finset ℕ) (scalar : ℕ)
    (h1 : 1∈S) (hr : scalar∈S) (ha : ∀i,(a.get i).Valid)
    (v : ℕ→Parts) (hv : Good S v) (k : ℕ) : Good S (iterate a 1 (scaleBody scalar) v k) := by
  induction k with
  | zero => exact hv
  | succ k ih =>
    exact (scaleBody scalar).evaluate_good S ⟨⟨h1,h1,hr⟩,trivial⟩ _
      (ih.update 1 (a.getD_valid ha _)) ⟨trivial,trivial⟩

theorem scale_iterate_width {n : ℕ} (a : Table n) (S : Finset ℕ) (scalar : ℕ)
    (hne : scalar≠1) (hr : scalar∈S) (W : ℕ) (hW : 1≤W)
    (ha : ∀i,(a.get i).Width W) (v : ℕ→Parts) (hv : WidthBank S W v) (k : ℕ) :
    WidthBank S (2*W+1) (iterate a 1 (scaleBody scalar) v k) := by
  induction k with
  | zero => exact hv.mono (by omega)
  | succ k ih =>
    have entry := a.getD_width W hW ha (n-1-k)
    have product : ((a.getD (n-1-k)).mul (v scalar)).Width (2*W+1) := by
      simpa only [two_mul] using entry.mul (hv scalar hr)
    have bank := ih.update 1 (entry.mono (by omega))
    have retained:=scale_retained a scalar hne v k
    simp only [scaleBody] at retained
    simpa only [iterate,scaleBody,Control.evaluate,Instruction.update,BinaryOp.eval,
      Function.update_self,Function.update_of_ne hne,retained]
      using bank.update 1 product

theorem scale_widthTrace {n : ℕ} (a : Table n) (S : Finset ℕ) (scalar : ℕ)
    (hne : scalar≠1) (hr : scalar∈S) (W : ℕ) (hW : 1≤W)
    (ha : ∀i,(a.get i).Width W) (v : ℕ→Parts) (hv : WidthBank S W v) (k : ℕ) :
    (scaleBody scalar).WidthTrace S (2*W+1) (loaded a 1 (scaleBody scalar) v k) := by
  refine ⟨(scale_iterate_width a S scalar hne hr W hW ha v hv k).update 1
    ((a.getD_width W hW ha _).mono (by omega)),trivial,?_⟩
  exact scale_iterate_width a S scalar hne hr W hW ha v hv (k+1)

theorem scale_values {n : ℕ} (a : Table n) (scalar : ℕ) (hne : scalar≠1) (v : ℕ→Parts) :
    mapValues a (scaleBody scalar) 1 v=fun i=>(a.get i).mul (v scalar) := by
  funext i
  have he : n-i.val=(n-1-i.val)+1 := by omega
  have hi : n-1-(n-1-i.val)=i.val := by omega
  simp only [mapValues,he,scale_result a scalar hne,hi,Table.getD,dite_eq_left i.isLt]

theorem scale_executes {n : ℕ} (a b : Table n) (S : Finset ℕ) (scalar : ℕ)
    (h1 : 1∈S) (hr : scalar∈S) (hne : scalar≠1)
    (v : ℕ→Parts) (W : ℕ) (hW : 1≤W) (hv : WidthBank S W v) (good : Good S v)
    (entryWidth : ∀i,(a.get i).Width W) (entryValid : ∀i,(a.get i).Valid)
    (haMeta : a.MetadataWidth (2*W+1)) (hbMeta : b.MetadataWidth (2*W+1))
    (hslot : 2*W+1≤addressValue b.width) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤2*W+1) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : SharedConversion.Ready S v s) (ha : a.Ready s) (hb : b.OutputReady s) :
    ∃cost t finalWord,Executes input tape (mapCode (scaleBody scalar) 1) cost s t ∧
      cost≤(n+1)*(13*xs.length+15)+n*mapStepCost (scaleBody scalar) (2*W+1) ∧
      SharedConversion.Ready S (iterate a 1 (scaleBody scalar) v n) t ∧ a.Ready t ∧
      (b.filled (fun i=>(a.get i).mul (v scalar)) 0).OutputReady t ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length ∧
      (∀i,((b.filled (fun i=>(a.get i).mul (v scalar)) 0).get i).value=
        (a.get i).value*(v scalar).value) ∧
      (∀limit,limit≤addressValue b.basePositive→limit≤addressValue b.baseNegative→
        limit≤addressValue b.baseDenominator→∀j,j<limit→t.val.memory j=s.val.memory j) := by
  obtain ⟨cost,t,word,e,hc,rt,at',bt,count,len,memory⟩ := map_executes a b S h1
    (scaleBody scalar) ⟨⟨h1,h1,hr⟩,trivial⟩ 1 h1 v (2*W+1) (by omega)
    haMeta hbMeta hslot hsep hdisjoint
    (fun k _=>scale_iterate_width a S scalar hne hr W hW entryWidth v hv k)
    (fun k _=>scale_widthTrace a S scalar hne hr W hW entryWidth v hv k)
    (fun k _=>(scale_iterate_good a S scalar h1 hr entryValid v good k).update 1
      (a.getD_valid entryValid _)) (fun _ _=>⟨trivial,trivial⟩)
    input tape xs origin hlen s hn hcount hs ha hb
  rw [scale_values a scalar hne] at bt
  refine ⟨cost,t,word,e,hc,rt,at',bt,count,len,?_,memory⟩
  intro i
  rw [Table.filled_get b _ (fun j=>((entryWidth j).mul (hv scalar hr)).mono (by omega)),Parts.mul_value]

#print axioms scale_executes
end Maxwell.Continuum.RationalDataflow.PartArray
