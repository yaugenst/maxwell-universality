import Maxwell.Cost.PhysicalMaterial.FlattenIndex

/-! The dense cell count is computed from stored box dimensions. It is an
ordinary canonical binary word, usable by initialization and serialization. -/
namespace Maxwell.Cost.PhysicalMaterial.DenseVolume
open Structured RationalAccumulator

abbrev Ready := FlattenIndex.Ready

def code : Code := .seq (FlattenIndex.code 250 276 276)
  (.seq (.call (WordTransfer.clone 322 328)) (.call (TapeOps.clear 322)))

def work : Finset ℕ := {0,1,2,3,322,328}
abbrev Frame := BinaryPrecision.Frame work

private theorem exact_frame {target : ℕ} {s t : BitRAMState}
    (hf : StoredProduct.Frame target s t) (hsmall : ∀ i,i<4→t.tapes i=s.tapes i) :
    BinaryPrecision.Frame {target} s t := by
  refine ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  intro i hi
  by_cases hh : i<4
  · exact hsmall i hh
  · exact hf.2.2.2.2.2.1 i (by omega) (by simpa using hi)

set_option maxRecDepth 8192 in
theorem executes (input : List Bool) (tape : ℕ→Bool) (nx ny nz B : ℕ) (s : Store)
    (hx : Word s.val 250 nx) (hy : Word s.val 251 ny) (hz : Word s.val 252 nz)
    (hzero : Word s.val 276 0) (hb : nx.bits.length≤B ∧ ny.bits.length≤B ∧ nz.bits.length≤B)
    (hr : Ready s.val) (h322 : Blank s.val 322) (h328 : Blank s.val 328) :
    ∃ cost t, cost≤21000*(B+2)^2 ∧ Executes input tape code cost s t ∧
      Word t.val 328 (nx*ny*nz) ∧ Blank t.val 322 ∧ Ready t.val ∧ Frame s.val t.val ∧
      (nx*ny*nz).bits.length≤3*B := by
  obtain ⟨ac,a,hac,ea,aw,ar,af,_⟩ := FlattenIndex.executes 250 276 276
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    input tape nx 0 0 ny nz B s hx hzero hzero hy hz
    ⟨hb.1,by simp,by simp,hb.2.1,hb.2.2⟩ hr h322
  simp only [Nat.add_zero] at aw
  obtain ⟨b,eb,bw,bf,bsmall⟩ := DecoderConstants.cloneStored 322 328 (by decide) (by decide) (by decide)
    input tape (nx*ny*nz) a aw (blank_of_eq (af.tapes 328 (by decide)) h328)
  have bf' := exact_frame bf bsmall
  obtain ⟨t,et,t322,tf,tsmall⟩ := DecoderConstants.clearStored 322 (by decide) input tape (nx*ny*nz) b
    (word_of_eq (bf'.tapes 322 (by decide)) aw)
  have tf' := exact_frame tf tsmall
  have ht := bf'.mono (b := {322,328}) (by decide) |>.trans (tf'.mono (by decide))
  have hxy := IndexedAddress.product_length_le nx.bits ny.bits
  have hxyz := IndexedAddress.product_length_le (nx*ny).bits nz.bits
  simp only [addressValue_bits] at hxy hxyz
  have hlen : (nx*ny*nz).bits.length≤3*B := by omega
  refine ⟨ac+((15*(nx*ny*nz).bits.length+17)+(6*(nx*ny*nz).bits.length+4)),t,?_,
    ea.seq (eb.seq et),word_of_eq (tf'.tapes 328 (by decide)) bw,t322,?_,
    (af.mono (by decide)).trans (ht.mono (by decide)),hlen⟩
  · have hsq : B+2≤(B+2)^2 := Nat.le_self_pow (by decide) _
    nlinarith
  · intro i hi
    exact blank_of_eq (ht.tapes i (by simp; omega)) (ar i hi)

end Maxwell.Cost.PhysicalMaterial.DenseVolume
