import Maxwell.Cost.PhysicalMaterial.Membership.Offset
import Maxwell.Cost.PhysicalMaterial.FixedSubtract
import Maxwell.Cost.IndexedAddress

/-! Fixed signed prototype offsets are compiled to literal addition or a
finite decrement block. Nonnegativity is supplied by the buffered geometry. -/
namespace Maxwell.Cost.PhysicalMaterial.Scatter
open Structured RationalAccumulator

abbrev Ready := Membership.Ready

def offsetCode (source target : ℕ) : ℤ → Code
  | .ofNat k => Membership.offsetCode source target k
  | .negSucc k => .seq (.call (WordTransfer.clone source target)) (FixedSubtract.code target (k+1))

abbrev offsetWork := Membership.offsetWork

def offsetFactor (delta : ℤ) : ℕ := 1000*(delta.natAbs+delta.natAbs.bits.length+5)

private theorem stored_frame {target : ℕ} {s t : BitRAMState}
    (h : StoredProduct.Frame target s t) : BinaryPrecision.Frame (offsetWork target) s t := by
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,?_⟩
  intro i hi
  simp only [offsetWork,Membership.offsetWork,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
  exact h.2.2.2.2.2.1 i (by omega) hi.2.2.2.2.1

set_option maxRecDepth 8192 in
set_option maxHeartbeats 500000 in
theorem offset_executes (source target : ℕ) (hs : 10≤source) (ht : 10≤target)
    (hst : source≠target) (ht292 : target≠292) (delta : ℤ) (n B : ℕ)
    (hn : n.bits.length≤B) (hroom : 0≤(n:ℤ)+delta)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hw : Word s.val source n)
    (hblank : Blank s.val target) (h292 : Blank s.val 292) (hr : Ready s.val) :
    ∃ cost t, cost≤offsetFactor delta*(B+1) ∧ Executes input tape (offsetCode source target delta) cost s t ∧
      Word t.val target ((n:ℤ)+delta).toNat ∧ Blank t.val 292 ∧ Ready t.val ∧
      BinaryPrecision.Frame (offsetWork target) s.val t.val := by
  cases delta with
  | ofNat k =>
    obtain ⟨cost,t,hc,he,hw',h292',hr',hf⟩ := Membership.offset_general source target k hs ht hst ht292
      input tape n s hw hblank h292 hr
    refine ⟨cost,t,?_,he,?_,h292',hr',hf⟩
    · change cost ≤ 1000*(k+k.bits.length+5)*(B+1)
      nlinarith
    · have hv : n+k = ((n:ℤ)+(Int.ofNat k)).toNat := by
        change n+k = ((n:ℤ)+(k:ℤ)).toNat
        omega
      simpa only [hv] using hw'
  | negSucc k =>
    obtain ⟨a,ea,aw,af,asmall⟩ := DecoderConstants.cloneStored source target (by omega) (by omega)
      hst input tape n s hw hblank
    obtain ⟨cost,t,et,hc,tw,tf⟩ := FixedSubtract.executes target (k+1) n (by omega)
      input tape a aw
    have af' := stored_frame af
    have tf' : BinaryPrecision.Frame (offsetWork target) a.val t.val :=
      tf.mono (by simp [offsetWork,Membership.offsetWork])
    refine ⟨15*n.bits.length+17+cost,t,?_,ea.seq et,?_,?_,?_,af'.trans tf'⟩
    · simp only [offsetFactor,Int.natAbs_negSucc]
      unfold FixedSubtract.costBound at hc
      nlinarith
    · have hv : n-(k+1) = ((n:ℤ)+Int.negSucc k).toNat := by omega
      simpa only [hv] using tw
    · exact blank_of_eq ((tf.tapes 292 (by simpa using Ne.symm ht292)).trans
        (af.2.2.2.2.2.1 292 (by decide) (Ne.symm ht292))) h292
    · intro i hi
      have hne : i≠target := by omega
      apply blank_of_eq (tf.tapes i (by simpa using hne))
      by_cases hi4 : i<4
      · exact blank_of_eq (asmall i hi4) (hr i hi)
      · exact blank_of_eq (af.2.2.2.2.2.1 i (by omega) hne) (hr i hi)

end Maxwell.Cost.PhysicalMaterial.Scatter
