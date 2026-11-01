import Maxwell.Cost.PhysicalEmit.Grid
import Maxwell.Cost.EmitNatural

/-! The shared box traversal emits its actual stored coordinates in x/y/z
order. This is the ambient-cell representation used by continuum instances. -/
namespace Maxwell.Cost.PhysicalEmit.Coordinates
open Structured RationalAccumulator
set_option maxHeartbeats 1800000

def body : Code := .seq (EmitNatural.code 240) (.seq (EmitNatural.code 241) (EmitNatural.code 242))
def record (x y z : ℕ) : List Bool := Codec.nat x++Codec.nat y++Codec.nat z
def code : Code := gridCode body
def cost (nx ny nz B : ℕ) : ℕ := (nx+1)*(ny+1)*(nz+1)*(216*B+246)

theorem body_executes (x y z : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hx : Word s.val 240 x) (hy : Word s.val 241 y) (hz : Word s.val 242 z) :
    ∃t,Executes input tape body (20*x.bits.length+24+(20*y.bits.length+24+(20*z.bits.length+24))) s t ∧
      t.val.output=(record x y z).reverse++s.val.output ∧ EmitNatural.Frame s t := by
  obtain ⟨ox,wx⟩:=hx
  obtain ⟨a,ea,oa,fa⟩:=EmitNatural.executes 240 x ox input tape s wx
  obtain ⟨oy,wy⟩:=word_of_eq (congrFun fa.2.2.2.2 241) hy
  obtain ⟨b,eb,ob,fb⟩:=EmitNatural.executes 241 y oy input tape a wy
  obtain ⟨oz,wz⟩:=word_of_eq (congrFun (fb.2.2.2.2.trans fa.2.2.2.2) 242) hz
  obtain ⟨t,et,ot,ft⟩:=EmitNatural.executes 242 z oz input tape b wz
  refine ⟨t,ea.seq (eb.seq et),?_,?_,⟩
  · rw [ot,ob,oa]
    simp only [record,List.reverse_append,List.append_assoc]
  · exact ⟨ft.1.trans (fb.1.trans fa.1),ft.2.1.trans (fb.2.1.trans fa.2.1),
      ft.2.2.1.trans (fb.2.2.1.trans fa.2.2.1),ft.2.2.2.1.trans (fb.2.2.2.1.trans fa.2.2.2.1),
      ft.2.2.2.2.trans (fb.2.2.2.2.trans fa.2.2.2.2)⟩

theorem executes (nx ny nz B : ℕ) (width : ∀a : Axis,(![nx,ny,nz] a).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (ready : LowerReady 0 ![nx,ny,nz] B s.val) :
    ∃steps t,Executes input tape code steps s t ∧ steps≤cost nx ny nz B ∧
      LowerReady 0 ![nx,ny,nz] B t.val ∧
      t.val.output=(gridWords ![nx,ny,nz] record).reverse++s.val.output ∧
      t.val.address=s.val.address ∧ t.val.memory=s.val.memory ∧ t.val.inputHead=s.val.inputHead ∧
      t.val.randomCursor=s.val.randomCursor ∧ (∀i∉loopTapes,t.val.tapes i=s.val.tapes i) := by
  let R : Store→Prop := fun t=>t.val.address=s.val.address ∧ t.val.memory=s.val.memory ∧
    t.val.inputHead=s.val.inputHead ∧ t.val.randomCursor=s.val.randomCursor ∧
    ∀i∉loopTapes,t.val.tapes i=s.val.tapes i
  have stable : ∀a b,LoopFrame loopTapes a.val b.val→R a→R b := by
    intro a b f h
    exact ⟨f.address.trans h.1,f.memory.trans h.2.1,f.inputHead.trans h.2.2.1,
      f.randomCursor.trans h.2.2.2.1,fun i hi=>(f.tapes i hi).trans (h.2.2.2.2 i hi)⟩
  have run : ∀x y z,x<nx→y<ny→z<nz→∀a,R a→LowerReady 3 ![nx,ny,nz] B a.val→
      Word a.val 240 x→Word a.val 241 y→Word a.val 242 z→
      ∃steps t,steps≤60*B+72 ∧ Executes input tape body steps a t ∧ R t ∧ Held 3 a.val t.val ∧
        t.val.output=(record x y z).reverse++a.val.output := by
    intro x y z hx hy hz a h _ wx wy wz
    have xb : x.bits.length≤B := by
      have w:=width 0
      change nx.bits.length≤B at w
      rw [Nat.size_eq_bits_len] at w ⊢
      exact (Nat.size_le_size hx.le).trans w
    have yb : y.bits.length≤B := by
      have w:=width 1
      change ny.bits.length≤B at w
      rw [Nat.size_eq_bits_len] at w ⊢
      exact (Nat.size_le_size hy.le).trans w
    have zb : z.bits.length≤B := by
      have w:=width 2
      change nz.bits.length≤B at w
      rw [Nat.size_eq_bits_len] at w ⊢
      exact (Nat.size_le_size hz.le).trans w
    obtain ⟨t,e,out,f⟩:=body_executes x y z input tape a wx wy wz
    exact ⟨_,t,by omega,e,⟨f.1.trans h.1,f.2.2.1.trans h.2.1,f.2.1.trans h.2.2.1,
      f.2.2.2.1.trans h.2.2.2.1,fun i hi=>(congrFun f.2.2.2.2 i).trans (h.2.2.2.2 i hi)⟩,
      ⟨fun i=>congrFun f.2.2.2.2 _,fun i _=>congrFun f.2.2.2.2 _,fun i _=>congrFun f.2.2.2.2 _⟩,out⟩
  obtain ⟨c,t,charge,e,h,r,_,out⟩:=grid ![nx,ny,nz] B (60*B+72) width body input tape R record
    stable run s ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩ ready
  refine ⟨c,t,e,?_,r,out,h⟩
  change c≤(nx+1)*(ny+1)*(nz+1)*(60*B+72+156*B+174) at charge
  simpa only [cost,show 60*B+72+156*B+174=216*B+246 by omega] using charge

#print axioms executes
end Maxwell.Cost.PhysicalEmit.Coordinates
