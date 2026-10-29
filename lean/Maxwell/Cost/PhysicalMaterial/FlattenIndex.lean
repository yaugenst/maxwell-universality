import Maxwell.Cost.PhysicalMaterial.Membership.Offset
import Maxwell.Cost.IndexedAddress

/-! Actual row-major index arithmetic for scatter points and streamed cells. -/
namespace Maxwell.Cost.PhysicalMaterial.FlattenIndex
open Structured RationalAccumulator

abbrev Ready := Membership.Ready

def work : Finset ℕ := {0,1,2,3,322}
abbrev Frame := BinaryPrecision.Frame work

def code (xBank yBank zBank : ℕ) : Code :=
  .seq (.call (WordTransfer.clone xBank 322))
    (.seq (DecoderTerm.multiplyCode 251 322)
      (.seq (DecoderConstants.addCode yBank 322)
        (.seq (DecoderTerm.multiplyCode 252 322) (DecoderConstants.addCode zBank 322))))

private theorem stored_frame {s t : BitRAMState} (h : StoredProduct.Frame 322 s t) : Frame s t := by
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,?_⟩
  intro i hi
  simp only [work,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
  exact h.2.2.2.2.2.1 i (by omega) hi.2.2.2.2

private theorem ready_frame {s t : BitRAMState} (hs : Ready s)
    (hf : Frame s t) (ht : ∀ i,i<4→Blank t i) : Ready t := by
  intro i hi
  by_cases hh : i<4
  · exact ht i hh
  · exact blank_of_eq (hf.tapes i (by simp only [work,Finset.mem_insert,Finset.mem_singleton,not_or]; omega)) (hs i hi)

private theorem word_frame {s t : BitRAMState} (hf : Frame s t) (bank n : ℕ)
    (hb : 10≤bank) (hne : bank≠322) (hw : Word s bank n) : Word t bank n :=
  word_of_eq (hf.tapes bank (by simp only [work,Finset.mem_insert,Finset.mem_singleton,not_or]; omega)) hw

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem executes (xBank yBank zBank : ℕ) (hxBank : 10≤xBank) (hyBank : 10≤yBank)
    (hzBank : 10≤zBank) (hxn : xBank≠322) (hyn : yBank≠322) (hzn : zBank≠322)
    (input : List Bool) (tape : ℕ→Bool) (x y z ny nz B : ℕ) (s : Store)
    (hx : Word s.val xBank x) (hy : Word s.val yBank y) (hz : Word s.val zBank z)
    (hny : Word s.val 251 ny) (hnz : Word s.val 252 nz)
    (hwidth : x.bits.length≤B ∧ y.bits.length≤B ∧ z.bits.length≤B ∧ ny.bits.length≤B ∧ nz.bits.length≤B)
    (hr : Ready s.val) (h322 : Blank s.val 322) :
    ∃ cost t, cost≤20000*(B+2)^2 ∧ Executes input tape (code xBank yBank zBank) cost s t ∧
      Word t.val 322 ((x*ny+y)*nz+z) ∧ Ready t.val ∧ Frame s.val t.val ∧
      ((x*ny+y)*nz+z).bits.length≤5*B+2 := by
  obtain ⟨a,ea,aw,af,asmall⟩ := DecoderConstants.cloneStored xBank 322 (by omega) (by decide)
    hxn input tape x s hx h322
  have af' := stored_frame af
  have ar : Ready a.val := ready_frame hr af' (fun i hi => blank_of_eq (asmall i hi) (hr i (by omega)))
  obtain ⟨bc,b,hbc,eb,bw,bsmall,bf⟩ := DecoderTerm.multiply 251 322 (by decide) (by decide) (by decide)
    input tape ny x a (word_frame af' 251 ny (by decide) (by decide) hny) aw (fun i hi => ar i (by omega))
  have bf' := stored_frame bf
  have br := ready_frame ar bf' bsmall
  have ab := af'.trans bf'
  obtain ⟨cc,c,hcc,ec,cw,csmall,cf⟩ := DecoderConstants.add yBank 322 (by omega) (by decide) hyn
    input tape y (ny*x) b (word_frame ab yBank y hyBank hyn hy) bw (fun i hi => br i (by omega))
  have cf' := stored_frame cf
  have cr := ready_frame br cf' csmall
  have abc := ab.trans cf'
  obtain ⟨dc,d,hdc,ed,dw,dsmall,df⟩ := DecoderTerm.multiply 252 322 (by decide) (by decide) (by decide)
    input tape nz (y+ny*x) c (word_frame abc 252 nz (by decide) (by decide) hnz) cw (fun i hi => cr i (by omega))
  have df' := stored_frame df
  have dr := ready_frame cr df' dsmall
  have abcd := abc.trans df'
  obtain ⟨ecost,t,hec,et,tw,tsmall,tf⟩ := DecoderConstants.add zBank 322 (by omega) (by decide) hzn
    input tape z (nz*(y+ny*x)) d (word_frame abcd zBank z hzBank hzn hz) dw (fun i hi => dr i (by omega))
  have tf' := stored_frame tf
  have hp := IndexedAddress.product_length_le ny.bits x.bits
  have hq := IndexedAddress.sum_length_le y.bits (ny*x).bits
  have ht := IndexedAddress.product_length_le nz.bits (y+ny*x).bits
  have hu := IndexedAddress.sum_length_le z.bits (nz*(y+ny*x)).bits
  simp only [addressValue_bits] at hp hq ht hu
  have hp' : (ny*x).bits.length≤2*B := by omega
  have hq' : (y+ny*x).bits.length≤3*B+1 := by omega
  have ht' : (nz*(y+ny*x)).bits.length≤4*B+1 := by omega
  have hb' : bc≤600*(2*B+3)^2 := by
    exact hbc.trans (Nat.mul_le_mul_left 600 (Nat.pow_le_pow_left (by omega) 2))
  have hd' : dc≤600*(4*B+4)^2 := by
    exact hdc.trans (Nat.mul_le_mul_left 600 (Nat.pow_le_pow_left (by omega) 2))
  have resultEq : z+nz*(y+ny*x) = (x*ny+y)*nz+z := by ac_rfl
  refine ⟨15*x.bits.length+17+(bc+(cc+(dc+ecost))),t,?_,ea.seq (eb.seq (ec.seq (ed.seq et))),
    ?_,ready_frame dr tf' tsmall,abcd.trans tf',?_⟩
  · nlinarith
  · simpa only [resultEq] using tw
  · rw [←resultEq]
    omega

end Maxwell.Cost.PhysicalMaterial.FlattenIndex
