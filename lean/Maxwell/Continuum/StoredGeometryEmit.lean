import Maxwell.Continuum.StoredGeometryState
import Maxwell.Cost.BankArray.Frame
import Maxwell.Cost.EmitNatural

namespace Maxwell.Continuum.GeometryOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator

theorem Context.of_tapes {n base width B : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants v : ℕ→ℕ} {s t : Store} (g : Context data base width B clock constants v s)
    (memory : t.val.memory=s.val.memory) (tapes : t.val.tapes=s.val.tapes) :
    Context data base width B clock constants v t:=
  ⟨⟨fun i hi=>word_of_eq (congrFun tapes i) (g.ready.bank i hi),
      g.ready.scratch.of_tapes (fun i _=>congrFun tapes i),blank_of_eq (congrFun tapes 7) g.ready.seven⟩,
    g.wordWidth,by simpa only [memory] using g.array,
    BankArray.word_of_eq (congrFun tapes 962) g.clockWord,g.fixed⟩

theorem Context.emit {n base width B : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants v : ℕ→ℕ} {s : Store} (g : Context data base width B clock constants v s)
    (source : ℕ) (hs : source∈ids) (input : List Bool) (tape : ℕ→Bool) :
    ∃t,Executes input tape (EmitNatural.code source) (20*(v source).bits.length+24) s t ∧
      Context data base width B clock constants v t ∧
      t.val.output=(Codec.nat (v source)).reverse++s.val.output ∧ EmitNatural.Frame s t:=by
  obtain ⟨origin,word⟩:=g.ready.bank source hs
  obtain ⟨t,ex,out,frame⟩:=EmitNatural.executes source (v source) origin input tape s word
  exact ⟨t,ex,g.of_tapes frame.2.2.1 frame.2.2.2.2,out,frame⟩

#print axioms Context.emit
end Maxwell.Continuum.GeometryOutput
