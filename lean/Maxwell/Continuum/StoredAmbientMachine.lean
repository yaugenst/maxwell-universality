import Maxwell.Continuum.StoredAmbientPlan
import Maxwell.Continuum.ContinuumAmbientEncoding

/-! Serialize every ambient unit cube from runtime dimensions, including the
actual list count. The iterator is shared with the discrete construction. -/
namespace Maxwell.Continuum.StoredAmbient
open Maxwell.Cost Maxwell.Cost.Structured RationalAccumulator
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def code : Code := .seq prepareCode (.seq (EmitNatural.code 258) PhysicalEmit.Coordinates.code)
def cost (v : ℕ→ℕ) (B : ℕ) : ℕ := prepareCost B+20*prepareWidth B+24+
  PhysicalEmit.Coordinates.cost (side v 0) (side v 1) (side v 2) (prepareWidth B)
def work : Finset ℕ := {0,1,2,3}∪outputs

theorem record_stream (nx ny nz : ℕ) :
    Codec.nat (nx*ny*nz)++PhysicalEmit.gridWords ![nx,ny,nz] PhysicalEmit.Coordinates.record=
      AmbientEncoding.bits nx ny nz := by
  have h:=PhysicalEmit.gridWords_cells (⟨nx,ny,nz⟩ : Target.Box) PhysicalEmit.Coordinates.record
  change PhysicalEmit.gridWords ![nx,ny,nz] PhysicalEmit.Coordinates.record=
    (Codec.triples nx ny nz).flatMap AmbientEncoding.cubeBits at h
  rw [h,AmbientEncoding.bits,Codec.list,AmbientEncoding.cubes_length]

theorem executes (v : ℕ→ℕ) (B : ℕ) (hB : 3≤B) (width : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val) :
    ∃steps t,Executes input tape code steps s t ∧ steps≤cost v B ∧
      t.val.output=(AmbientEncoding.bits (side v 0) (side v 1) (side v 2)).reverse++s.val.output ∧
      PhysicalEmit.LowerReady 0 (side v) (prepareWidth B) t.val ∧ NatAssign.Scratch t.val ∧
      t.val.address=s.val.address ∧ t.val.memory=s.val.memory ∧ t.val.inputHead=s.val.inputHead ∧
      t.val.randomCursor=s.val.randomCursor ∧ (∀i∉work,t.val.tapes i=s.val.tapes i) := by
  obtain ⟨c,a,e,charge,stored,blank,words,ready,frame⟩:=prepare_executes v B hB width input tape s bank scratch
  obtain ⟨origin,w⟩:=stored 258 (by decide)
  obtain ⟨b,eb,out,fb⟩:=EmitNatural.executes 258 (prepared v 258) origin input tape a w
  have readyB : PhysicalEmit.LowerReady 0 (side v) (prepareWidth B) b.val := by
    refine ⟨fun i => word_of_eq (congrFun fb.2.2.2.2 _) (ready.dimensions i),?_,?_⟩
    · intro i hi
      obtain ⟨n,hn,hw⟩:=ready.coordinates i hi
      exact ⟨n,hn,word_of_eq (congrFun fb.2.2.2.2 _) hw⟩
    · intro i hi
      obtain ⟨w,hl,hw⟩:=ready.counters i hi
      exact ⟨w,hl,BankArray.word_of_eq (congrFun fb.2.2.2.2 _) hw⟩
  have sides : ![side v 0,side v 1,side v 2]=side v := by funext j;fin_cases j <;> rfl
  have sideWidth : ∀j:PhysicalEmit.Axis,(![side v 0,side v 1,side v 2] j).bits.length≤prepareWidth B := by
    intro j
    rw [sides,←prepared_sides v j]
    exact words _ (by fin_cases j <;> decide)
  obtain ⟨d,t,et,dt,rt,ot,address,memory,ih,random,keep⟩:=PhysicalEmit.Coordinates.executes
    (side v 0) (side v 1) (side v 2) (prepareWidth B) sideWidth input tape b (sides ▸ readyB)
  refine ⟨c+(20*(prepared v 258).bits.length+24+d),t,e.seq (eb.seq et),?_,?_,?_,?_,
    address.trans (fb.1.trans frame.address),memory.trans (fb.2.2.1.trans frame.memory),
    ih.trans (fb.2.1.trans frame.inputHead),random.trans (fb.2.2.2.1.trans frame.randomCursor),?_⟩
  · have volumeWidth:=words 258 (by decide)
    unfold cost
    omega
  · rw [ot,out,frame.output,prepared_volume]
    rw [←List.append_assoc,←List.reverse_append,record_stream]
  · simpa only [sides] using rt
  · intro i hi
    apply blank_of_eq ((keep i (by simp only [PhysicalEmit.loopTapes,Finset.mem_insert,Finset.mem_singleton];omega)).trans
      (congrFun fb.2.2.2.2 i)) (blank i hi)
  · intro i hi
    have loop : i∉PhysicalEmit.loopTapes := by
      simp only [work,outputs,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
      simp only [PhysicalEmit.loopTapes,Finset.mem_insert,Finset.mem_singleton]
      tauto
    exact (keep i loop).trans ((congrFun fb.2.2.2.2 i).trans (frame.tapes i hi))

#print axioms executes
end Maxwell.Continuum.StoredAmbient
