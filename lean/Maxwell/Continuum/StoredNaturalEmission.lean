import Maxwell.Cost.EmitNatural
import Maxwell.Cost.Structured.NatAssign

/-! A fixed finite header emits runtime natural words. The instruction
sequence depends only on its static ports, never on the stored values. -/
namespace Maxwell.Continuum.StoredNatural
open Maxwell.Cost Maxwell.Cost.Structured

def code : List ℕ→Code
  | [] => .skip
  | port::ports => .seq (EmitNatural.code port) (code ports)

def bits (ports : List ℕ) (values : ℕ→ℕ) : List Bool := ports.flatMap (fun i => Codec.nat (values i))

theorem executes (ports : List ℕ) (values : ℕ→ℕ) (B : ℕ)
    (hw : ∀i∈ports,(values i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : ∀i∈ports,RationalAccumulator.Word s.val i (values i)) :
    ∃cost t,Executes input tape (code ports) cost s t ∧
      cost≤ports.length*(20*B+24)+1 ∧
      t.val.output=(bits ports values).reverse++s.val.output ∧ EmitNatural.Frame s t := by
  induction ports generalizing s with
  | nil => exact ⟨1,s,Executes.skip s,by simp,by simp [bits],rfl,rfl,rfl,rfl,rfl⟩
  | cons i ports ih =>
    obtain ⟨origin,word⟩ := hs i (by simp)
    obtain ⟨s0,e0,out0,f0⟩ := EmitNatural.executes i (values i) origin input tape s word
    have keep (j : ℕ) (hj : j∈ports) : RationalAccumulator.Word s0.val j (values j) :=
      RationalAccumulator.word_of_eq (congrFun f0.2.2.2.2 j) (hs j (by simp [hj]))
    obtain ⟨c1,t,e1,hc1,out1,f1⟩ := ih (fun j hj=>hw j (by simp [hj])) s0 keep
    refine ⟨20*(values i).bits.length+24+c1,t,e0.seq e1,?_,?_,
      f1.1.trans f0.1,f1.2.1.trans f0.2.1,f1.2.2.1.trans f0.2.2.1,
      f1.2.2.2.1.trans f0.2.2.2.1,f1.2.2.2.2.trans f0.2.2.2.2⟩
    · have hi := hw i (by simp)
      simp only [List.length_cons]
      nlinarith only [hc1,hi]
    · rw [out1,out0]
      simp only [bits,List.flatMap_cons,List.reverse_append,List.append_assoc]

def continuumHeaderPorts : List ℕ := [720,721,722,723,724,725,726,727]
def continuumHeaderCode : Code := code continuumHeaderPorts

theorem continuumHeader_executes (values : ℕ→ℕ) (B : ℕ)
    (hw : ∀i∈continuumHeaderPorts,(values i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : ∀i∈continuumHeaderPorts,RationalAccumulator.Word s.val i (values i)) :
    ∃cost t,Executes input tape continuumHeaderCode cost s t ∧ cost≤160*B+193 ∧
      t.val.output=(bits continuumHeaderPorts values).reverse++s.val.output ∧ EmitNatural.Frame s t := by
  obtain ⟨cost,t,ex,hc,out,frame⟩ := executes continuumHeaderPorts values B hw input tape s hs
  have hc' : cost≤160*B+193 := by
    simp only [continuumHeaderPorts,List.length_cons,List.length_nil] at hc
    omega
  exact ⟨cost,t,ex,hc',out,frame⟩

#print axioms continuumHeader_executes
end Maxwell.Continuum.StoredNatural
