import Maxwell.Continuum.StoredGeometryTerminal

/-! A mediator record uses two consecutive points of the same stored path.
The next point becomes the previous point by three charged word copies. -/
namespace Maxwell.Continuum.GeometryOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def copyNextPlan : List NatAssign.Instruction := [.copy 979 976,.copy 980 977,.copy 981 978]
def copyNextValues (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values copyNextPlan v

theorem copyNext_get (v : ℕ→ℕ) (j : Fin 3) : copyNextValues v (976+j.val)=v (979+j.val) := by
  fin_cases j <;> simp [copyNextValues,copyNextPlan,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]

theorem copyNext_preserves (v : ℕ→ℕ) (k : ℕ) (hk : k≠976 ∧ k≠977 ∧ k≠978) :
    copyNextValues v k=v k := by
  simp only [copyNextValues,copyNextPlan,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,Function.update_of_ne hk.1,
    Function.update_of_ne hk.2.1,Function.update_of_ne hk.2.2]

theorem copyNext_executes {n base width B : ℕ} {values : Vector ℕ n} {clock : List Bool}
    {constants v : ℕ→ℕ} {s : Store} (h : Context values base width B clock constants v s)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,Executes input tape (NatAssign.code copyNextPlan) cost s t ∧ cost≤2^23*(B+3)^2 ∧
      Context values base width B clock constants (copyNextValues v) t ∧
      BinaryPrecision.Frame {0,1,2,3,976,977,978} s.val t.val := by
  have valid : ∀a∈copyNextPlan,a.Valid ids := by simp [copyNextPlan,NatAssign.Instruction.Valid,ids]
  obtain ⟨cost,t,ex,hc,bt,zt,ft⟩ := NatAssign.executes ids
    (fun i hi=>(by omega : 4≤960).trans (ids_ge i hi)) copyNextPlan valid v input tape s h.ready.bank h.ready.natural
  have changes : NatAssign.changes copyNextPlan={0,1,2,3,976,977,978} := by decide
  rw [changes] at ft
  have costB := hc.trans (NatAssign.price_bound ids copyNextPlan valid v B h.wordWidth
    (by simp [copyNextPlan,NatAssign.Instruction.literalWidth]))
  have rt : Ready (copyNextValues v) t := h.ready.stage bt zt (ft.mono (by decide))
  have hcost : cost≤2^23*(B+3)^2 := by
    change cost≤3000*8^3*(B+2)^2 at costB
    nlinarith only [costB,Nat.zero_le B]
  refine ⟨cost,t,ex,hcost,⟨rt,?_,?_,?_,?_⟩,ft⟩
  · intro k hk
    by_cases h0 : k=976
    · subst k
      change (copyNextValues v (976+(0:Fin 3).val)).bits.length≤B
      rw [copyNext_get]
      exact h.wordWidth 979 (by decide)
    by_cases h1 : k=977
    · subst k
      change (copyNextValues v (976+(1:Fin 3).val)).bits.length≤B
      rw [copyNext_get]
      exact h.wordWidth 980 (by decide)
    by_cases h2 : k=978
    · subst k
      change (copyNextValues v (976+(2:Fin 3).val)).bits.length≤B
      rw [copyNext_get]
      exact h.wordWidth 981 (by decide)
    rw [copyNext_preserves v k ⟨h0,h1,h2⟩]
    exact h.wordWidth k hk
  · simpa only [ft.memory] using h.array
  · exact BankArray.word_of_eq (ft.tapes 962 (by decide)) h.clockWord
  · intro k hk
    rw [copyNext_preserves v k (by
      have hs : k∉({976,977,978}:Finset ℕ) := by
        exact Finset.disjoint_left.mp (by decide : Disjoint fixedIds {976,977,978}) hk
      simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hs)]
    exact h.fixed k hk

def mediatorCoordinate {n : ℕ} (values : Vector ℕ n) (constants : ℕ→ℕ) (cursor : ℕ) (j : Fin 3) : ℕ :=
  constants 982+constants (983+j.val)*(arrayValue values (cursor+j.val)+arrayValue values (cursor+3+j.val))

def mediatorBits {n : ℕ} (values : Vector ℕ n) (constants : ℕ→ℕ) (cursor : ℕ) : List Bool :=
  Codec.int (mediatorCoordinate values constants cursor 0:ℤ)++
    Codec.int (mediatorCoordinate values constants cursor 1:ℤ)++
    Codec.int (mediatorCoordinate values constants cursor 2:ℤ)++Codec.nat (constants 966)

def mediatorStepCode : Code := .seq (readPlanCode (tripleTargets true))
  (.seq (recordCode false) (NatAssign.code copyNextPlan))

theorem mediator_coordinate {n : ℕ} (values : Vector ℕ n) (constants v : ℕ→ℕ) (cursor : ℕ)
    (hf : ∀k∈fixedIds,v k=constants k) (hi : v 971=cursor+3)
    (hp : ∀j:Fin 3,v (976+j.val)=arrayValue values (cursor+j.val)) (j : Fin 3) :
    coordinateValue false j (readPlanValues values (tripleTargets true) v)=
      mediatorCoordinate values constants cursor j := by
  let w := readPlanValues values (tripleTargets true) v
  have hw (k : ℕ) (hk : k∈fixedIds) : w k=constants k := by
    change readPlanValues values (tripleTargets true) v k=constants k
    rw [readPlanValues_preserves values (tripleTargets true) v k]
    · exact hf k hk
    · intro hh;exact tripleTargets_fixed true k hh hk
    · intro hh;subst k;exact (by decide : (971:ℕ)∉fixedIds) hk
  have hprev : w (976+j.val)=arrayValue values (cursor+j.val) := by
    rw [show w (976+j.val)=v (976+j.val) from readPlanValues_preserves values _ _ _
      (by fin_cases j <;> decide) (by omega)]
    exact hp j
  have hnext := tripleValues_get values true v j
  simp only [ite_true,hi] at hnext
  change w (979+j.val)=_ at hnext
  change coordinateValue false j w=mediatorCoordinate values constants cursor j
  simp only [coordinateValue,Bool.false_eq_true,ite_false,hw 982 (by decide),
    hw (983+j.val) (by fin_cases j <;> decide),hprev,hnext,mediatorCoordinate]

theorem mediatorStep_executes {n base width B : ℕ} {values : Vector ℕ n} {clock : List Bool}
    {constants v : ℕ→ℕ} {s : Store} (h : Context values base width B clock constants v s)
    (hw : 0<width) (hB : width≤B) (hlen : clock.length=width) (hn : n.bits.length≤B)
    (hfit : ∀i,(values.get i).bits.length≤width)
    (hb : constants 960=base) (hv : constants 961=width) (ho : constants 970=1)
    (cursor : ℕ) (hi : v 971=cursor+3) (hix : cursor+6≤n)
    (hp : ∀j:Fin 3,v (976+j.val)=arrayValue values (cursor+j.val))
    (hc : ∀j,(mediatorCoordinate values constants cursor j).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t w,Executes input tape mediatorStepCode cost s t ∧ cost≤2^30*(B+3)^2 ∧
      Context values base width B clock constants w t ∧ w 971=cursor+6 ∧
      (∀j:Fin 3,w (976+j.val)=arrayValue values (cursor+3+j.val)) ∧
      t.val.output=(mediatorBits values constants cursor).reverse++s.val.output ∧
      (∀k,10 ≤ k → k∉({971,976,977,978,979,980,981,987}:Finset ℕ) → t.val.tapes k=s.val.tapes k) := by
  obtain ⟨c0,a,e0,hc0,ca,fa⟩ := h.read_plan (tripleTargets true) (tripleTargets_valid true)
    (tripleTargets_fixed true) hw hB hlen hn hfit hb hv ho
    (by rw [tripleTargets_length,hi];omega) input tape
  have hcoord := mediator_coordinate values constants v cursor h.fixed hi hp
  obtain ⟨c1,b,e1,hc1,cb,ob,fb⟩ := ca.record false (fun j=>by rw [hcoord];exact hc j) input tape
  obtain ⟨c2,t,e2,hc2,ct,ft⟩ := copyNext_executes cb input tape
  refine ⟨c0+(c1+c2),t,_,e0.seq (e1.seq e2),?_,ct,?_,?_,?_,?_⟩
  · rw [tripleTargets_length] at hc0
    nlinarith only [hc0,hc1,hc2,Nat.zero_le B]
  · rw [copyNext_preserves _ 971 (by decide),Function.update_of_ne (by decide : (971:ℕ)≠987),
      readPlanValues_cursor,tripleTargets_length,hi]
  · intro j
    rw [copyNext_get,Function.update_of_ne (by omega : 979+j.val≠987)]
    simpa only [ite_true,hi] using tripleValues_get values true v j
  · rw [ft.output,ob,fa.output]
    have hl := ca.fixed 966 (by decide)
    simp only [recordBits,hcoord,hl,mediatorBits]
  · intro k hk hnot
    have ne : k≠971 ∧ k≠976 ∧ k≠977 ∧ k≠978 ∧ k≠979 ∧ k≠980 ∧ k≠981 ∧ k≠987 := by
      simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hnot
    exact (ft.tapes k (by simp only [Finset.mem_insert,Finset.mem_singleton];omega)).trans
      ((fb.tapes k (by simp only [Finset.mem_insert,Finset.mem_singleton];omega)).trans
        (fa.tapes k hk (by simpa [tripleTargets] using
          (show k≠979 ∧ k≠980 ∧ k≠981 ∧ k≠971 by tauto))))

#print axioms mediatorStep_executes
end Maxwell.Continuum.GeometryOutput
