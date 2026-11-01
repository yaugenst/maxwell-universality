import Maxwell.Continuum.SourceRoutingGeometryDifference
import Maxwell.Continuum.SourceRoutingGeometryLoad
import Maxwell.Continuum.SourceGeometryCursorCount
import Maxwell.Cost.Structured.NatAssign.Values

/-! Compute the number of emitted wells from the packed geometry cursor and
the retained vertex and edge counts. No second geometry traversal is used. -/
namespace Maxwell.Continuum.Parameters.GeometryCountMachine
open Maxwell.Cost Maxwell.Cost.Structured
open Maxwell.Cost.RoutingPorts.Complete
open GeometryArithmetic
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

def loaded (v : ℕ→ℕ) (cursor vertices edges : ℕ) : ℕ→ℕ :=
  Function.update (Function.update (Function.update v 1202 cursor) 1203 vertices) 1204 edges
def instructions : List NatAssign.Instruction :=
  [.literal 1205 2,.multiply 1202 1205,.literal 1206 3,.multiply 1203 1206,
   .literal 1207 11,.multiply 1204 1207,.add 1207 1206,.literal 1207 0,.literal 1208 3]
def prepared (v : ℕ→ℕ) (cursor vertices edges : ℕ) : ℕ→ℕ :=
  NatAssign.values instructions (loaded v cursor vertices edges)
def subtracted (v : ℕ→ℕ) (cursor vertices edges : ℕ) : ℕ→ℕ :=
  Function.update (prepared v cursor vertices edges) 1207 (2*cursor-(3*vertices+11*edges))
def output (v : ℕ→ℕ) (cursor vertices edges : ℕ) : ℕ→ℕ :=
  divided (subtracted v cursor vertices edges) 1207 1208 1209 1210
def code : Code := .seq (loadCode 1253 1202) (.seq (loadCode 141 1203)
  (.seq (loadCode 153 1204) (.seq (NatAssign.code instructions)
    (.seq (WordDifference.code 1205 1206 1207) (divisionCode 1207 1208 1209 1210)))))

theorem valid : ∀a∈instructions,a.Valid ids := by
  simp [instructions,NatAssign.Instruction.Valid,ids,controls]

theorem prepared_values (v : ℕ→ℕ) (cursor vertices edges : ℕ) :
    prepared v cursor vertices edges 1205=2*cursor ∧
    prepared v cursor vertices edges 1206=3*vertices+11*edges ∧
    prepared v cursor vertices edges 1207=0 ∧
    prepared v cursor vertices edges 1208=3 := by
  simp [prepared,instructions,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,loaded,Nat.mul_comm,Nat.add_comm]

theorem prepared_quotient (v : ℕ→ℕ) (cursor vertices edges : ℕ) (i : ℕ)
    (hi : i∈RationalDataflow.NaturalQuotient.workPorts) : prepared v cursor vertices edges i=v i := by
  simp only [RationalDataflow.NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl
  all_goals simp [prepared,instructions,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,loaded]

theorem output_count (v : ℕ→ℕ) (cursor vertices edges : ℕ) :
    output v cursor vertices edges 1209=(2*cursor-3*vertices-11*edges)/3 := by
  simp only [output,divided,Function.update_of_ne (by decide : (1209:ℕ)≠1210),
    Function.update_self,subtracted,Function.update_of_ne (by decide : (1208:ℕ)≠1207),
    (prepared_values v cursor vertices edges).2.2.2]
  omega

theorem output_side (v : ℕ→ℕ) (cursor vertices edges : ℕ) :
    output v cursor vertices edges 1200=v 1200 := by
  simp [output,divided,subtracted,prepared,instructions,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,loaded]

theorem loaded_width (v : ℕ→ℕ) (cursor vertices edges B : ℕ)
    (width : ∀i∈ids,(v i).bits.length≤B)
    (hc : cursor.bits.length≤B) (hv : vertices.bits.length≤B) (he : edges.bits.length≤B) :
    ∀i∈ids,(loaded v cursor vertices edges i).bits.length≤B := by
  intro i hi
  by_cases h4 : i=1204
  · subst i;simpa [loaded] using he
  · by_cases h3 : i=1203
    · subst i;simpa [loaded] using hv
    · by_cases h2 : i=1202
      · subst i;simpa [loaded] using hc
      · simpa only [loaded,Function.update_of_ne h4,Function.update_of_ne h3,
          Function.update_of_ne h2] using width i hi

#print axioms output_count
end Maxwell.Continuum.Parameters.GeometryCountMachine
