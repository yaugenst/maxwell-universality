import Maxwell.Continuum.StoredWellPath
import Maxwell.Continuum.StoredNaturalEmission

/-! Charged cursor resets, counter loads, and the single well-list header.
All values are read from the actual geometry and payload banks. -/
namespace Maxwell.Continuum.WellOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def cursorPlan (paths : Bool) : List NatAssign.Instruction :=
  if paths then [.copy 963 971,.multiply 969 971] else [.literal 971 0]

def cursorCode (paths : Bool) : Code := NatAssign.code (cursorPlan paths)

theorem cursor_values (paths : Bool) (v : ℕ→ℕ) :
    NatAssign.values (cursorPlan paths) v=Function.update v 971 (if paths then v 963*v 969 else 0) := by
  cases paths <;> funext k <;> by_cases hk:k=971 <;>
    simp [cursorPlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,hk,Nat.mul_comm]

theorem cursor_executes {n base width BG J P B first : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context data base width BG clock constants gv s)
    (paths : Bool) (vertices : ℕ) (hv : constants 963=vertices) (hthree : constants 969=3)
    (hspan : 3*vertices≤n) (hn : n.bits.length≤BG)
    (strengths : Table J) (profile template : List Bool) (rv : ℕ→Parts)
    (p : WellPayload.State strengths P B first profile template rv s)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,Executes input tape (cursorCode paths) cost s t ∧ cost≤2^23*(BG+3)^2 ∧
      GeometryOutput.Context data base width BG clock constants
        (Function.update gv 971 (if paths then 3*vertices else 0)) t ∧
      WellPayload.State strengths P B first profile template rv t ∧ t.val.output=s.val.output ∧
      (∀k∈({972,973}:Finset ℕ),t.val.tapes k=s.val.tapes k) := by
  have valid : ∀a∈cursorPlan paths,a.Valid GeometryOutput.ids := by
    cases paths <;> simp [cursorPlan,NatAssign.Instruction.Valid,GeometryOutput.ids]
  obtain ⟨cost,t,ex,hc,bt,zt,ft⟩ := NatAssign.executes GeometryOutput.ids
    (fun i hi=>(by omega : 4≤960).trans (GeometryOutput.ids_ge i hi)) (cursorPlan paths) valid gv
    input tape s g.ready.bank g.ready.natural
  have changes : NatAssign.changes (cursorPlan paths)={0,1,2,3,971} := by cases paths <;> decide
  rw [changes] at ft
  have eval : NatAssign.values (cursorPlan paths) gv=Function.update gv 971 (if paths then 3*vertices else 0) := by
    rw [cursor_values,g.fixed 963 (by decide),g.fixed 969 (by decide),hv,hthree,Nat.mul_comm vertices 3]
  rw [eval] at bt
  have rt := g.ready.stage bt zt (ft.mono (by decide))
  have hcursor : (if paths then 3*vertices else 0).bits.length≤BG := by
    cases paths with
    | false => simp
    | true =>
      have hh : (3*vertices).bits.length≤n.bits.length := by
        simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hspan
      exact hh.trans hn
  have gt : GeometryOutput.Context data base width BG clock constants
      (Function.update gv 971 (if paths then 3*vertices else 0)) t := by
    refine ⟨rt,?_,by simpa only [ft.memory] using g.array,
      BankArray.word_of_eq (ft.tapes 962 (by decide)) g.clockWord,?_⟩
    · intro k hk
      by_cases he : k=971
      · subst k;simpa only [Function.update_self] using hcursor
      · rw [Function.update_of_ne he];exact g.wordWidth k hk
    · intro k hk
      rw [Function.update_of_ne (by intro he;subst k;exact (by decide : (971:ℕ)∉GeometryOutput.fixedIds) hk)]
      exact g.fixed k hk
  have pt := p.geometry_frame gt.ready ft.memory (fun k hk hr=>ft.tapes k (by
    simp only [Finset.mem_insert,Finset.mem_singleton];omega))
  have hcost := hc.trans (NatAssign.price_bound GeometryOutput.ids (cursorPlan paths) valid gv BG g.wordWidth
    (by cases paths <;> simp [cursorPlan,NatAssign.Instruction.literalWidth]))
  refine ⟨cost,t,ex,?_,gt,pt,ft.output,fun k hk=>ft.tapes k (by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk ⊢;omega)⟩
  cases paths with
  | false =>
    change cost≤24000*(BG+2)^2 at hcost
    nlinarith only [hcost,Nat.zero_le BG]
  | true =>
    change cost≤192000*(BG+2)^2 at hcost
    nlinarith only [hcost,Nat.zero_le BG]

theorem loadCounter_executes {n base width BG J P B first : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context data base width BG clock constants gv s)
    (source : ℕ) (hs : source∈GeometryOutput.ids)
    (strengths : Table J) (profile template : List Bool) (rv : ℕ→Parts)
    (p : WellPayload.State strengths P B first profile template rv s)
    (old : List Bool) (hold : BankArray.Word s.val 972 old) (hOld : old.length≤BG)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,Executes input tape (WordReplace.code source 972) cost s t ∧ cost≤21*BG+21 ∧
      GeometryOutput.Context data base width BG clock constants gv t ∧
      WellPayload.State strengths P B first profile template rv t ∧
      BankArray.Word t.val 972 (gv source).bits ∧ t.val.output=s.val.output ∧
      t.val.tapes 973=s.val.tapes 973 := by
  obtain ⟨cost,t,ex,hc,gt,wt,ft⟩ := GeometryOutput.loadCounter_executes g source 972 hs (by decide)
    old hold hOld input tape
  have pt := p.geometry_frame gt.ready ft.memory (fun k hk hr=>ft.tapes k hk (by
    simp only [Finset.mem_singleton];omega))
  exact ⟨cost,t,ex,hc,gt,pt,wt,ft.output,ft.tapes 973 (by decide) (by decide)⟩

theorem header_executes {n base width BG J P B first : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context data base width BG clock constants gv s)
    (strengths : Table J) (profile template : List Bool) (rv : ℕ→Parts)
    (p : WellPayload.State strengths P B first profile template rv s)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,Executes input tape (EmitNatural.code 988) cost s t ∧ cost≤20*BG+24 ∧
      GeometryOutput.Context data base width BG clock constants gv t ∧
      WellPayload.State strengths P B first profile template rv t ∧
      t.val.output=(Codec.nat (gv 988)).reverse++s.val.output ∧ EmitNatural.Frame s t := by
  obtain ⟨origin,word⟩ := g.ready.bank 988 (by decide)
  obtain ⟨t,ex,out,ft⟩ := EmitNatural.executes 988 (gv 988) origin input tape s word
  have pt := p.emit_frame ft
  have gt := WellPayload.geometry_context_frame g pt ft.2.2.1
    (fun k _ _ _=>congrFun ft.2.2.2.2 k)
  exact ⟨_,t,ex,by have := g.wordWidth 988 (by decide);omega,gt,pt,out,ft⟩

#print axioms cursor_executes
#print axioms loadCounter_executes
#print axioms header_executes
end Maxwell.Continuum.WellOutput
