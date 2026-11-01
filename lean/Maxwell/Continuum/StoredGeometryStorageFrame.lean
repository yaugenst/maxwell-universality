import Maxwell.Continuum.StoredGeometryState

/-! Geometry storage is retained across any operation preserving its words and memory. -/
namespace Maxwell.Continuum
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator

theorem GeometryOutput.Context.storage_frame {n base width B : ℕ} {data : Vector ℕ n}
    {clock : List Bool} {constants v : ℕ→ℕ} {s t : Store}
    (g : GeometryOutput.Context data base width B clock constants v s)
    (memory : t.val.memory=s.val.memory)
    (keep : ∀i∈GeometryOutput.ids,t.val.tapes i=s.val.tapes i)
    (clockKeep : t.val.tapes 962=s.val.tapes 962)
    (scratch : BankArray.Scratch t.val) (seven : Blank t.val 7):
    GeometryOutput.Context data base width B clock constants v t:=
  ⟨⟨fun i hi=>word_of_eq (keep i hi) (g.ready.bank i hi),scratch,seven⟩,
    g.wordWidth,by simpa only [memory] using g.array,
    BankArray.word_of_eq clockKeep g.clockWord,g.fixed⟩

end Maxwell.Continuum
