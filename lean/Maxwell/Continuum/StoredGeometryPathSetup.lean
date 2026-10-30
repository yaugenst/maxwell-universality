import Maxwell.Continuum.StoredGeometryCounter
import Maxwell.Continuum.StoredGeometryTerminal

/-! A path pass reads its actual length header, installs and trims the
inner counter, then reads the first point. The two supported callers use
one trim for edges and two trims for interior vertices. -/
namespace Maxwell.Continuum.GeometryOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def pathSetupCode (trim : ℕ) : Code := .seq (readPlanCode [974])
  (.seq (WordReplace.code 974 973) (.seq (trimCounterCode 973 trim)
    (readPlanCode (tripleTargets false))))

theorem pathSetup_executes {n base width B : ℕ} {values : Vector ℕ n} {clock : List Bool}
    {constants v : ℕ→ℕ} {s : Store} (h : Context values base width B clock constants v s)
    (hw : 0<width) (hB : width≤B) (hlen : clock.length=width) (hn : n.bits.length≤B)
    (hfit : ∀i,(values.get i).bits.length≤width)
    (hb : constants 960=base) (hv : constants 961=width) (ho : constants 970=1)
    (start count trim : ℕ) (hstart : v 971=start) (hspan : start+4≤n)
    (hcount : arrayValue values start=count) (htrim : trim≤count) (htrim2 : trim≤2)
    (old : List Bool) (hold : BankArray.Word s.val 973 old) (hOld : old.length≤B)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t word origin w,Executes input tape (pathSetupCode trim) cost s t ∧ cost≤2^26*(B+3)^2 ∧
      Context values base width B clock constants w t ∧ w 971=start+4 ∧
      (∀j:Fin 3,w (976+j.val)=arrayValue values (start+1+j.val)) ∧
      t.val.tapes 973=BitTape.shifted word origin ∧ word.length=count.bits.length ∧
      addressValue word=count-trim ∧ t.val.output=s.val.output ∧
      (∀k,10 ≤ k → k∉({971,973,974,976,977,978}:Finset ℕ) → t.val.tapes k=s.val.tapes k) := by
  obtain ⟨c0,a,e0,hc0,ca,fa⟩ := h.read_plan [974] (by simp [ids]) (by simp [fixedIds])
    hw hB hlen hn hfit hb hv ho (by simp only [List.length_cons,List.length_nil];omega) input tape
  let va := readPlanValues values [974] v
  have h974 : va 974=count := by
    simp only [va,readPlanValues,readAdvanceValues,
      Function.update_of_ne (by decide : (974:ℕ)≠971),Function.update_self,hstart,hcount]
  have h971 : va 971=start+1 := by simp only [va,readPlanValues_cursor,hstart,List.length_cons,List.length_nil]
  have olda : BankArray.Word a.val 973 old := BankArray.word_of_eq
    (fa.tapes 973 (by decide) (by decide)) hold
  obtain ⟨c1,b,e1,hc1,cb,wb,fb⟩ := loadCounter_executes ca 974 973 (by decide) (by decide)
    old olda hOld input tape
  rw [show readPlanValues values [974] v 974=count from h974] at wb
  obtain ⟨origin,wordb⟩ := wb
  obtain ⟨c,word,ec,cc,wc,wl,wv,fc⟩ := trimCounter_executes 973 trim (by decide) input tape
    count.bits origin b cb wordb (by simpa only [addressValue_bits] using htrim)
  obtain ⟨c3,t,e3,hc3,ct,ft⟩ := cc.read_plan (tripleTargets false) (tripleTargets_valid false)
    (tripleTargets_fixed false) hw hB hlen hn hfit hb hv ho
    (by rw [tripleTargets_length];change va 971+3≤n;rw [h971];omega) input tape
  have countB : count.bits.length≤B := by
    have hh : (va 974).bits.length≤B := ca.wordWidth 974 (by decide)
    simpa only [h974] using hh
  refine ⟨c0+(c1+(trim*(13*count.bits.length+14)+1+c3)),t,word,origin,_,
    e0.seq (e1.seq (ec.seq e3)),?_,ct,?_,?_,?_,wl,?_,?_,?_⟩
  · simp only [List.length_cons,List.length_nil,tripleTargets_length] at hc0 hc3
    have htrimcost : trim*(13*count.bits.length+14)≤2*(13*B+14) :=
      Nat.mul_le_mul htrim2 (by omega)
    nlinarith only [hc0,hc1,hc3,htrimcost,Nat.zero_le B]
  · rw [readPlanValues_cursor,tripleTargets_length]
    change va 971+3=start+4
    rw [h971]
  · intro j
    simpa only [Bool.false_eq_true,ite_false,h971] using tripleValues_get values false va j
  · exact (ft.tapes 973 (by decide) (by decide)).trans wc
  · simpa only [addressValue_bits] using wv
  · exact ft.output.trans (fc.output.trans (fb.output.trans fa.output))
  · intro k hk hnot
    have ne : k≠971 ∧ k≠973 ∧ k≠974 ∧ k≠976 ∧ k≠977 ∧ k≠978 := by
      simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hnot
    exact (ft.tapes k hk (by simpa [tripleTargets] using
      (show k≠976 ∧ k≠977 ∧ k≠978 ∧ k≠971 by tauto))).trans
      ((fc.tapes k hk (by simpa only [Finset.mem_singleton] using ne.2.1)).trans
        ((fb.tapes k hk (by simpa only [Finset.mem_singleton] using ne.2.1)).trans
          (fa.tapes k hk (by simp only [List.toFinset_cons,List.toFinset_nil,Finset.union_singleton,
            Finset.mem_insert,Finset.notMem_empty,or_false];tauto))))

#print axioms pathSetup_executes
end Maxwell.Continuum.GeometryOutput
