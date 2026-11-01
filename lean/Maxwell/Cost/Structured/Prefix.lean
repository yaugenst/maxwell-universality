import Maxwell.Cost.Structured.Syntax

/-! A fixed sequential prefix may be shared by different branches without
replaying input or changing the state passed to the selected continuation. -/
namespace Maxwell.Cost.Structured

inductive Code.Prefix (first : Code) : Code→Code→Prop where
  | here (rest : Code) : Prefix first (.seq first rest) rest
  | seq {whole rest : Code} (h : Prefix first whole rest) (after : Code) :
      Prefix first (.seq whole after) (.seq rest after)

theorem Code.Prefix.split {first whole rest : Code} (h : Prefix first whole rest)
    {input : List Bool} {tape : ℕ→Bool} {cost : ℕ} {s t : Store}
    (run : Executes input tape whole cost s t) :
    ∃a b middle,cost=a+b ∧ Executes input tape first a s middle ∧
      Executes input tape rest b middle t := by
  induction h generalizing cost s t with
  | here rest =>
    cases run with
    | seq firstRun secondRun => exact ⟨_,_,_,rfl,firstRun,secondRun⟩
  | seq h after ih =>
    cases run with
    | seq firstRun secondRun =>
      obtain ⟨a,b,middle,eq,ef,er⟩:=ih firstRun
      exact ⟨a,_,middle,by omega,ef,er.seq secondRun⟩

#print axioms Code.Prefix.split
end Maxwell.Cost.Structured
