import Maxwell.Continuum.StoredGeometryState

/-! One actual terminal record: read its three consecutive routing words,
apply the physical affine map, and write the exact placement record. -/
namespace Maxwell.Continuum.GeometryOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def tripleTargets (next : Bool) : List ℕ := if next then [979,980,981] else [976,977,978]

theorem tripleTargets_length (next : Bool) : (tripleTargets next).length=3 := by cases next <;> rfl

theorem tripleTargets_valid (next : Bool) :
    ∀t∈tripleTargets next,t∈ids ∧ t≠960 ∧ t≠961 ∧ t≠962 ∧ t≠971 ∧ t≠970 := by
  cases next <;> simp [tripleTargets,ids]

theorem tripleTargets_fixed (next : Bool) : ∀t∈tripleTargets next,t∉fixedIds := by
  cases next <;> simp [tripleTargets,fixedIds]

theorem tripleValues_get {n : ℕ} (values : Vector ℕ n) (next : Bool) (v : ℕ→ℕ) (j : Fin 3) :
    readPlanValues values (tripleTargets next) v ((if next then 979 else 976)+j.val)=
      arrayValue values (v 971+j.val) := by
  cases next <;> fin_cases j <;>
    simp [tripleTargets,readPlanValues,readAdvanceValues,Nat.add_assoc]

def terminalCoordinate {n : ℕ} (values : Vector ℕ n) (constants : ℕ→ℕ) (cursor : ℕ) (j : Fin 3) : ℕ :=
  constants 982+constants (983+j.val)*(2*arrayValue values (cursor+j.val))

def terminalBits {n : ℕ} (values : Vector ℕ n) (constants : ℕ→ℕ) (cursor : ℕ) : List Bool :=
  Codec.int (terminalCoordinate values constants cursor 0:ℤ)++
    Codec.int (terminalCoordinate values constants cursor 1:ℤ)++
    Codec.int (terminalCoordinate values constants cursor 2:ℤ)++Codec.nat (constants 966)

def terminalStepCode : Code := .seq (readPlanCode (tripleTargets false)) (recordCode true)

theorem terminal_coordinate {n : ℕ} (values : Vector ℕ n) (constants v : ℕ→ℕ)
    (hf : ∀k∈fixedIds,v k=constants k) (j : Fin 3) :
    coordinateValue true j (readPlanValues values (tripleTargets false) v)=
      terminalCoordinate values constants (v 971) j := by
  let w := readPlanValues values (tripleTargets false) v
  have hw (k : ℕ) (hk : k∈fixedIds) : w k=constants k := by
    change readPlanValues values (tripleTargets false) v k=constants k
    rw [readPlanValues_preserves values (tripleTargets false) v k]
    · exact hf k hk
    · intro hh;exact tripleTargets_fixed false k hh hk
    · intro hh;subst k;exact (by decide : (971:ℕ)∉fixedIds) hk
  have hpoint := tripleValues_get values false v j
  simp only [Bool.false_eq_true,ite_false] at hpoint
  change w (976+j.val)=_ at hpoint
  change coordinateValue true j w=terminalCoordinate values constants (v 971) j
  simp only [coordinateValue,ite_true,hw 982 (by decide),
    hw (983+j.val) (by fin_cases j <;> decide),hpoint,terminalCoordinate]
  ring

theorem terminal_bits {n : ℕ} (values : Vector ℕ n) (constants v : ℕ→ℕ)
    (hf : ∀k∈fixedIds,v k=constants k) :
    recordBits true (readPlanValues values (tripleTargets false) v)=terminalBits values constants (v 971) := by
  have hL : readPlanValues values (tripleTargets false) v 966=constants 966 := by
    rw [readPlanValues_preserves values (tripleTargets false) v 966 (by decide) (by decide)]
    exact hf 966 (by decide)
  simp only [recordBits,terminal_coordinate values constants v hf,hL,terminalBits]

theorem terminalStep_executes {n base width B : ℕ} {values : Vector ℕ n} {clock : List Bool}
    {constants v : ℕ→ℕ} {s : Store} (h : Context values base width B clock constants v s)
    (hw : 0<width) (hB : width≤B) (hlen : clock.length=width) (hn : n.bits.length≤B)
    (hfit : ∀i,(values.get i).bits.length≤width)
    (hb : constants 960=base) (hv : constants 961=width) (ho : constants 970=1)
    (hix : v 971+3≤n)
    (hc : ∀j,(terminalCoordinate values constants (v 971) j).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t w,Executes input tape terminalStepCode cost s t ∧ cost≤2^30*(B+3)^2 ∧
      Context values base width B clock constants w t ∧ w 971=v 971+3 ∧
      t.val.output=(terminalBits values constants (v 971)).reverse++s.val.output ∧
      (∀k,10 ≤ k → k∉({971,976,977,978,987}:Finset ℕ) → t.val.tapes k=s.val.tapes k) := by
  obtain ⟨c0,a,e0,hc0,ca,fa⟩ := h.read_plan (tripleTargets false) (tripleTargets_valid false)
    (tripleTargets_fixed false) hw hB hlen hn hfit hb hv ho
    (by simpa only [tripleTargets_length] using hix) input tape
  have ha : ∀j,(coordinateValue true j (readPlanValues values (tripleTargets false) v)).bits.length≤B := by
    intro j;rw [terminal_coordinate values constants v h.fixed];exact hc j
  obtain ⟨c1,t,e1,hc1,ct,ot,ft⟩ := ca.record true ha input tape
  refine ⟨c0+c1,t,_,e0.seq e1,?_,ct,?_,?_,?_⟩
  · rw [tripleTargets_length] at hc0
    nlinarith only [hc0,hc1,Nat.zero_le B]
  · simp only [Function.update_of_ne (by decide : (971:ℕ)≠987),
      readPlanValues_cursor,tripleTargets_length]
  · rw [ot,terminal_bits values constants v h.fixed,fa.output]
  · intro k hk hnot
    have hn' : k≠971 ∧ k≠976 ∧ k≠977 ∧ k≠978 ∧ k≠987 := by
      simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hnot
    exact (ft.tapes k (by simp only [Finset.mem_insert,Finset.mem_singleton];omega)).trans
      (fa.tapes k hk (by simpa [tripleTargets] using
        (show k≠976 ∧ k≠977 ∧ k≠978 ∧ k≠971 by tauto)))

#print axioms terminalStep_executes
end Maxwell.Continuum.GeometryOutput
