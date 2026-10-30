import Maxwell.Continuum.StoredGeometryCursor

/-! A finite, fixed list of successive packed reads. In particular each
three-coordinate read is one fixed program, independent of geometry size. -/
namespace Maxwell.Continuum.GeometryOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def arrayValue {n : ℕ} (values : Vector ℕ n) (i : ℕ) : ℕ :=
  if h : i<n then values.get ⟨i,h⟩ else 0

def readPlanCode : List ℕ → Code
  | [] => .skip
  | target::rest => .seq (readAdvanceCode target) (readPlanCode rest)

def readPlanValues {n : ℕ} (values : Vector ℕ n) : List ℕ → (ℕ→ℕ) → (ℕ→ℕ)
  | [],v => v
  | target::rest,v => readPlanValues values rest
      (readAdvanceValues v target (arrayValue values (v 971)))

theorem readPlanValues_preserves {n : ℕ} (values : Vector ℕ n) (targets : List ℕ)
    (v : ℕ→ℕ) (k : ℕ) (hk : k∉targets) (hi : k≠971) :
    readPlanValues values targets v k=v k := by
  induction targets generalizing v with
  | nil => rfl
  | cons t ts ih =>
    have hk' : k≠t ∧ k∉ts := by simpa only [List.mem_cons,not_or] using hk
    simp only [readPlanValues,ih _ hk'.2,readAdvanceValues,
      Function.update_of_ne hi,Function.update_of_ne hk'.1]

theorem readPlanValues_cursor {n : ℕ} (values : Vector ℕ n) (targets : List ℕ) (v : ℕ→ℕ) :
    readPlanValues values targets v 971=v 971+targets.length := by
  induction targets generalizing v with
  | nil => simp only [readPlanValues,List.length_nil,Nat.add_zero]
  | cons t ts ih =>
    simp only [readPlanValues,ih,readAdvanceValues,Function.update_self,List.length_cons]
    omega

theorem readPlan_executes {n : ℕ} (values : Vector ℕ n) (targets : List ℕ)
    (ht : ∀t∈targets,t∈ids ∧ t≠960 ∧ t≠961 ∧ t≠962 ∧ t≠971 ∧ t≠970)
    (base width B : ℕ) (clock : List Bool) (hwidth : 0<width) (hwidthB : width≤B)
    (hlen : clock.length=width) (hn : n.bits.length≤B)
    (hfit : ∀i,(values.get i).bits.length≤width)
    (v : ℕ→ℕ) (hv : ∀i∈ids,(v i).bits.length≤B)
    (hbase : v 960=base) (hwidthv : v 961=width) (hone : v 970=1)
    (hindex : v 971+targets.length≤n)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready v s)
    (hclock : BankArray.Word s.val 962 clock)
    (harray : BitArray.Represents s.val.memory base width (IncidenceEncoding.words width values)) :
    ∃cost t,Executes input tape (readPlanCode targets) cost s t ∧
      cost≤targets.length*(2^22*(B+3)^2)+1 ∧ Ready (readPlanValues values targets v) t ∧
      (∀k∈ids,((readPlanValues values targets v) k).bits.length≤B) ∧
      BitArray.Represents t.val.memory base width (IncidenceEncoding.words width values) ∧
      BankArray.Word t.val 962 clock ∧ ReadFrame (targets.toFinset∪{971}) s.val t.val := by
  induction targets generalizing v s with
  | nil =>
    exact ⟨1,s,Executes.skip s,by simp,hs,hv,harray,hclock,
      ⟨rfl,rfl,rfl,rfl,fun _ _ _=>rfl⟩⟩
  | cons target rest ih =>
    obtain ⟨hti,h0,h1,h2,hc,ho⟩ := ht target (by simp)
    have hi : v 971<n := by simp only [List.length_cons] at hindex;omega
    let i : Fin n := ⟨v 971,hi⟩
    obtain ⟨c0,a,e0,hc0,ra,wa,aa,ca,fa⟩ := readAdvance_executes values base width B clock
      hwidth hwidthB hlen hn target hti h0 h1 h2 hc ho v hv hbase hwidthv i rfl hone
      (hfit i) input tape s hs hclock harray
    have ha : arrayValue values (v 971)=values.get i := by simp only [arrayValue,dite_eq_left hi];rfl
    let va := readAdvanceValues v target (values.get i)
    have vb : va 960=base := by simp only [va,readAdvanceValues,
      Function.update_of_ne (by decide : (960:ℕ)≠971),Function.update_of_ne h0.symm,hbase]
    have vw : va 961=width := by simp only [va,readAdvanceValues,
      Function.update_of_ne (by decide : (961:ℕ)≠971),Function.update_of_ne h1.symm,hwidthv]
    have vo : va 970=1 := by simp only [va,readAdvanceValues,
      Function.update_of_ne (by decide : (970:ℕ)≠971),Function.update_of_ne ho.symm,hone]
    have vi : va 971+rest.length≤n := by
      simp only [va,readAdvanceValues,Function.update_self]
      simp only [List.length_cons] at hindex
      omega
    obtain ⟨c1,t,e1,hc1,rt,wt,arrt,ct,ft⟩ := ih (fun j hj=>ht j (by simp only [List.mem_cons];exact Or.inr hj))
      va wa vb vw vo vi a ra ca aa
    have hvfinal : readPlanValues values (target::rest) v=readPlanValues values rest va := by
      simp only [readPlanValues,ha,va]
    refine ⟨c0+c1,t,e0.seq e1,?_,hvfinal.symm ▸ rt,hvfinal.symm ▸ wt,arrt,ct,?_⟩
    · simp only [List.length_cons]
      nlinarith only [hc0,hc1]
    · refine ⟨ft.memory.trans fa.memory,ft.inputHead.trans fa.inputHead,
        ft.randomCursor.trans fa.randomCursor,ft.output.trans fa.output,?_⟩
      intro k hk hnot
      have hh : k≠target ∧ k∉rest ∧ k≠971 := by
        simpa only [Finset.mem_union,Finset.mem_singleton,List.mem_toFinset,List.mem_cons,not_or,
          and_assoc] using hnot
      exact (ft.tapes k hk (by simpa only [Finset.mem_union,Finset.mem_singleton,
        List.mem_toFinset,not_or] using hh.2)).trans
        (fa.tapes k hk (by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using
          (And.intro hh.1 hh.2.2)))

#print axioms readPlan_executes
end Maxwell.Continuum.GeometryOutput
