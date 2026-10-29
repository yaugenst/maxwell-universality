import Maxwell.Cost.SourceCircuit.ArithmeticReady

namespace Maxwell.Cost.SourceCircuit.ArithmeticPass
open Structured

def boundaryCode : Code := .branch 30 FinalizeRow.code .skip

def stepCode : Code := .seq Marker.code (.seq boundaryCode CompileRecord.code)

def firstCode : Code := .seq Marker.code CompileRecord.code

set_option maxRecDepth 16384 in
theorem boundary_executes (input : List Bool) (tape : ℕ → Bool) (clock : List Bool)
    (precision width : ℕ) (boundary : Bool) (d : Data) (s : Store)
    (hc : clock.length = width) (hr : Ready clock precision d s) (hv : Shape width d)
    (hroom : addressValue d.next+1+d.terms.length < 2^width)
    (hb : s.val.registers 30 = boundary) :
    ∃ cost t, cost ≤ (if boundary then FinalizeRow.costBound d.terms.length width d.counter.length else 0)+2 ∧
      Executes input tape boundaryCode cost s t ∧
      Ready clock precision (if boundary then finish d else d) t ∧
      Shape width (if boundary then finish d else d) ∧ Persistent s t ∧
      (∀ j, j ∉ RowSum.outputWork → (j=4 ∨ 10≤j) → t.val.tapes j = s.val.tapes j) := by
  cases boundary with
  | false => exact ⟨2,s,by simp,.no hb (.skip s),hr,hv,Persistent.refl s,fun _ _ _ => rfl⟩
  | true =>
    obtain ⟨cost,t,hcost,et,tr,tf,keep⟩ := finish_executes input tape clock precision width d s hc hr hv hroom
    exact ⟨1+cost,t,by simp; omega,.yes hb et,tr,finish_shape d hv hroom,tf,keep⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
theorem step_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool) (clock : List Bool)
    (precision width : ℕ) (boundary : Bool) (r : AllocationPass.Record n)
    (records : List (AllocationPass.Record n)) (flags : List Bool) (d : Data)
    (preceding suffix beforeLeaves leafSuffix beforeMarkers followingMarkers : List Bool) (s : Store)
    (hc : clock.length = width) (hp : r.bits.length = precision)
    (hr : Ready clock precision d s) (hv : Valid width (r::records) (boundary::flags) d)
    (h24 : s.val.tapes 24 = Increment.cursor beforeMarkers (boundary::followingMarkers) 0)
    (h85 : s.val.tapes 85 = NormalizedRecordParser.cursor
      (preceding ++ (r.wire ++ suffix)) preceding.length)
    (h98 : s.val.tapes 98 = Increment.cursor beforeLeaves (d.leaves.flatten ++ leafSuffix) 0) :
    ∃ cost t,
      cost ≤ (if boundary then FinalizeRow.costBound d.terms.length width d.counter.length else 0)+
        CompileRecord.bound r.row r.column.val precision width width+7 ∧
      Executes input tape stepCode cost s t ∧ Ready clock precision (body boundary r d) t ∧
      Valid width records flags (body boundary r d) ∧
      t.val.tapes 85 = NormalizedRecordParser.cursor (preceding ++ (r.wire ++ suffix))
        (preceding.length+r.wire.length) ∧
      t.val.tapes 98 = Increment.cursor
        (beforeLeaves ++ (d.leaves.take (r.bits.count true)).flatten)
        ((d.leaves.drop (r.bits.count true)).flatten ++ leafSuffix) 0 ∧
      t.val.tapes 24 = Increment.cursor (beforeMarkers ++ [boundary]) followingMarkers 0 ∧
      Persistent s t ∧ t.val.tapes 100 = s.val.tapes 100 := by
  obtain ⟨m,em,mb,_,m24,mf⟩ := Marker.executes input tape beforeMarkers followingMarkers boundary s h24
  have hfinishRoom : addressValue d.next+1+d.terms.length < 2^width := by
    have hroom := hv.room
    simp only [reserve,List.map_cons,List.sum_cons,List.length_cons] at hroom
    omega
  obtain ⟨bc,b,hbc,eb,br,bv,bf,bkeep⟩ := boundary_executes input tape clock precision width
    boundary d m hc (hr.marker mf) hv.shape hfinishRoom mb
  let current := if boundary then finish d else d
  have leaves : current.leaves = d.leaves := by cases boundary <;> rfl
  have enough : r.bits.count true ≤ current.leaves.length := by
    rw [leaves]
    have hn := hv.leavesCount
    simp only [AllocationPass.occurrences,List.map_cons,List.sum_cons] at hn
    omega
  have valid := valid_body boundary r records flags d hv
  have termRoom : addressValue current.next + termGateCost r < 2^width := by
    have hh := valid.room
    change addressValue (term r current).next + reserve records flags (term r current) < 2^width at hh
    rw [term_next] at hh
    omega
  obtain ⟨rc,t,hrc,et,tr,t85,t98,tf,tkeep⟩ := term_executes input tape clock precision width r current
    preceding suffix beforeLeaves leafSuffix b hc hp br bv enough termRoom
    ((bkeep 85 (by decide) (by omega)).trans ((mf.tapes 85 (by omega)).trans h85))
    (by rw [leaves]; exact (bkeep 98 (by decide) (by omega)).trans ((mf.tapes 98 (by omega)).trans h98))
  have execution : Executes input tape stepCode (5+(bc+rc)) s t := em.seq (eb.seq et)
  refine ⟨5+(bc+rc),t,?_,execution,tr,valid,t85,by simpa [leaves] using t98,
    (tkeep 24 (by decide) (by omega)).trans ((bkeep 24 (by decide) (by omega)).trans m24),
    (persistent_marker mf).trans (bf.trans tf),execution.protectsTape 100 (by decide)⟩
  have counterBound := bv.counterLength
  change current.counter.length ≤ width at counterBound
  unfold CompileRecord.bound at hrc ⊢
  omega

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
theorem first_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool) (clock : List Bool)
    (precision width : ℕ) (marker : Bool) (r : AllocationPass.Record n) (d : Data)
    (preceding suffix beforeLeaves leafSuffix beforeMarkers followingMarkers : List Bool) (s : Store)
    (hc : clock.length = width) (hp : r.bits.length = precision)
    (hr : Ready clock precision d s) (hv : Shape width d)
    (hleaves : r.bits.count true ≤ d.leaves.length)
    (hroom : addressValue d.next + termGateCost r < 2^width)
    (h24 : s.val.tapes 24 = Increment.cursor beforeMarkers (marker::followingMarkers) 0)
    (h85 : s.val.tapes 85 = NormalizedRecordParser.cursor
      (preceding ++ (r.wire ++ suffix)) preceding.length)
    (h98 : s.val.tapes 98 = Increment.cursor beforeLeaves (d.leaves.flatten ++ leafSuffix) 0) :
    ∃ cost t, cost ≤ CompileRecord.bound r.row r.column.val precision width width+5 ∧
      Executes input tape firstCode cost s t ∧ Ready clock precision (term r d) t ∧
      t.val.tapes 85 = NormalizedRecordParser.cursor (preceding ++ (r.wire ++ suffix))
        (preceding.length+r.wire.length) ∧
      t.val.tapes 98 = Increment.cursor
        (beforeLeaves ++ (d.leaves.take (r.bits.count true)).flatten)
        ((d.leaves.drop (r.bits.count true)).flatten ++ leafSuffix) 0 ∧
      t.val.tapes 24 = Increment.cursor (beforeMarkers ++ [marker]) followingMarkers 0 ∧
      Persistent s t ∧ t.val.tapes 100 = s.val.tapes 100 := by
  obtain ⟨m,em,_,_,m24,mf⟩ := Marker.executes input tape beforeMarkers followingMarkers marker s h24
  obtain ⟨cost,t,hcost,et,tr,t85,t98,tf,keep⟩ := term_executes input tape clock precision width r d
    preceding suffix beforeLeaves leafSuffix m hc hp (hr.marker mf) hv hleaves hroom
    ((mf.tapes 85 (by omega)).trans h85) ((mf.tapes 98 (by omega)).trans h98)
  have execution : Executes input tape firstCode (5+cost) s t := em.seq et
  refine ⟨5+cost,t,?_,execution,tr,t85,t98,
    (keep 24 (by decide) (by omega)).trans m24,(persistent_marker mf).trans tf,
    execution.protectsTape 100 (by decide)⟩
  have hcounter := hv.counterLength
  unfold CompileRecord.bound at hcost ⊢
  omega

end Maxwell.Cost.SourceCircuit.ArithmeticPass
