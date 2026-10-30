import Maxwell.Continuum.StoredGeometryCoordinate
import Maxwell.Continuum.StoredPlacementStep

/-! The actual three-coordinate calculation/emission and common length word
produce precisely the placement-record format used by the continuum file. -/
namespace Maxwell.Continuum.GeometryOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def recordCode (terminal : Bool) : Code := .seq (coordinateCode terminal 0)
  (.seq (coordinateCode terminal 1) (.seq (coordinateCode terminal 2) (EmitNatural.code 966)))

def recordBits (terminal : Bool) (v : ℕ→ℕ) : List Bool :=
  Codec.int (coordinateValue terminal 0 v:ℤ)++Codec.int (coordinateValue terminal 1 v:ℤ)++
    Codec.int (coordinateValue terminal 2 v:ℤ)++Codec.nat (v 966)

theorem coordinateValue_update (terminal : Bool) (j : Fin 3) (v : ℕ→ℕ) (x : ℕ) :
    coordinateValue terminal j (Function.update v 987 x)=coordinateValue terminal j v := by
  cases terminal <;> fin_cases j <;> simp [coordinateValue]

theorem updated_width (v : ℕ→ℕ) (B x : ℕ) (hv : ∀i∈ids,(v i).bits.length≤B)
    (hx : x.bits.length≤B) : ∀i∈ids,((Function.update v 987 x) i).bits.length≤B := by
  intro i hi
  by_cases he : i=987
  · subst i;simpa only [Function.update_self] using hx
  · simpa only [Function.update_of_ne he] using hv i hi

theorem OutputFrame.trans {work : Finset ℕ} {s t u : BitRAMState}
    (f : OutputFrame work s t) (g : OutputFrame work t u) : OutputFrame work s u :=
  ⟨g.memory.trans f.memory,g.inputHead.trans f.inputHead,g.randomCursor.trans f.randomCursor,
    fun i hi => (g.tapes i hi).trans (f.tapes i hi)⟩

theorem OutputFrame.emit {work : Finset ℕ} {s t u : Store}
    (f : OutputFrame work s.val t.val) (g : EmitNatural.Frame t u) : OutputFrame work s.val u.val :=
  ⟨g.2.2.1.trans f.memory,g.2.1.trans f.inputHead,g.2.2.2.1.trans f.randomCursor,
    fun i hi => (congrFun g.2.2.2.2 i).trans (f.tapes i hi)⟩

theorem record_executes (terminal : Bool) (v : ℕ→ℕ) (B : ℕ)
    (hv : ∀i∈ids,(v i).bits.length≤B)
    (hc : ∀j,(coordinateValue terminal j v).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready v s) :
    ∃cost t,Executes input tape (recordCode terminal) cost s t ∧
      cost≤2^28*(B+3)^2 ∧ Ready (Function.update v 987 (coordinateValue terminal 2 v)) t ∧
      (∀i∈ids,((Function.update v 987 (coordinateValue terminal 2 v)) i).bits.length≤B) ∧
      t.val.output=(recordBits terminal v).reverse++s.val.output ∧
      OutputFrame {0,1,2,3,987} s.val t.val := by
  obtain ⟨c0,s0,e0,hc0,r0,out0,f0⟩ := coordinate_executes terminal 0 v B hv input tape s hs
  let v0 := Function.update v 987 (coordinateValue terminal 0 v)
  have w0 := updated_width v B _ hv (hc 0)
  obtain ⟨c1,s1,e1,hc1,r1,out1,f1⟩ := coordinate_executes terminal 1 v0 B w0 input tape s0 r0
  have evalues1 : Function.update v0 987 (coordinateValue terminal 1 v0)=
      Function.update v 987 (coordinateValue terminal 1 v) := by
    simp only [v0,coordinateValue_update,Function.update_idem]
  rw [evalues1] at r1
  let v1 := Function.update v 987 (coordinateValue terminal 1 v)
  have w1 := updated_width v B _ hv (hc 1)
  obtain ⟨c2,s2,e2,hc2,r2,out2,f2⟩ := coordinate_executes terminal 2 v1 B w1 input tape s1 r1
  have evalues2 : Function.update v1 987 (coordinateValue terminal 2 v1)=
      Function.update v 987 (coordinateValue terminal 2 v) := by
    simp only [v1,coordinateValue_update,Function.update_idem]
  rw [evalues2] at r2
  have hL : Word s2.val 966 (v 966) := by
    simpa only [Function.update_of_ne (by decide : (966:ℕ)≠987)] using r2.bank 966 (by decide)
  obtain ⟨origin,hL⟩ := hL
  obtain ⟨t,e3,out3,f3⟩ := EmitNatural.executes 966 (v 966) origin input tape s2 hL
  refine ⟨c0+(c1+(c2+(20*(v 966).bits.length+24))),t,e0.seq (e1.seq (e2.seq e3)),?_,
    r2.emit f3,updated_width v B _ hv (hc 2),?_,((f0.trans f1).trans f2).emit f3⟩
  · have hl := hv 966 (by decide)
    nlinarith only [hc0,hc1,hc2,hl,Nat.zero_le B]
  · rw [out3,out2,out1,out0]
    simp only [v0,v1,coordinateValue_update,recordBits,List.reverse_append,List.append_assoc]

theorem recordBits_format (terminal : Bool) (v : ℕ→ℕ) (z : ℕ→ℤ) (i : ℕ)
    (hz : ∀j:Fin 3,z (3*i+j.val)=(coordinateValue terminal j v:ℤ)) :
    recordBits terminal v=RationalDataflow.StoredPlacement.recordBits z (v 966) i := by
  simp only [recordBits,RationalDataflow.StoredPlacement.recordBits,←hz 0,←hz 1,←hz 2]
  rfl

#print axioms record_executes
end Maxwell.Continuum.GeometryOutput
