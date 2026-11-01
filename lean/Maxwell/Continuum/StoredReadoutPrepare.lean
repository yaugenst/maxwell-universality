import Maxwell.Continuum.StoredGeometryCounter
import Maxwell.Continuum.StoredGeometryTerminalLoop
import Maxwell.Cost.EmitNatural

/-! The readout traversal starts at the actual circuit-size offset and uses
the actual source dimension. The packed geometry is read in place. -/
namespace Maxwell.Continuum.GeometryOutput.Readout
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def ports : Finset ℕ := ids∪{500,503}
def plan : List NatAssign.Instruction := [.copy 503 971,.multiply 969 971,.copy 500 989]
def prepareCode : Code := NatAssign.code plan

def loaded (v : ℕ→ℕ) (first count : ℕ) := Function.update (Function.update v 500 count) 503 first
def prepared (v : ℕ→ℕ) (first count : ℕ) := Function.update (Function.update v 971 (3*first)) 989 count

theorem valid : ∀a∈plan,a.Valid ports:=by simp [plan,NatAssign.Instruction.Valid,ports,ids]
theorem changes : NatAssign.changes plan={0,1,2,3,971,989}:=by decide

theorem loaded_inside (v : ℕ→ℕ) (first count k : ℕ) (hk : k∈ids) : loaded v first count k=v k:=by
  have h:=ids_ge k hk
  simp only [loaded,Function.update_of_ne (by omega : k≠503),Function.update_of_ne (by omega : k≠500)]

theorem values (v : ℕ→ℕ) (first count : ℕ) (hthree : v 969=3) :
    NatAssign.values plan (loaded v first count)=loaded (prepared v first count) first count:=by
  funext k
  by_cases h0:k=500 <;> by_cases h1:k=503 <;> by_cases h2:k=971 <;> by_cases h3:k=989 <;>
    simp [plan,loaded,prepared,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,h0,h1,h2,h3,hthree,Nat.mul_comm]

theorem prepare_executes {n base width B : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants v : ℕ→ℕ} {s : Store} (g : Context data base width B clock constants v s)
    (first count : ℕ) (hfirst : first.bits.length≤B) (hcount : count.bits.length≤B)
    (hcursor : (3*first).bits.length≤B) (hthree : constants 969=3)
    (firstWord : Word s.val 503 first) (countWord : Word s.val 500 count)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,Executes input tape prepareCode cost s t ∧ cost≤2^22*(B+2)^2 ∧
      Context data base width B clock constants (prepared v first count) t ∧
      BinaryPrecision.Frame {0,1,2,3,971,989} s.val t.val:=by
  have bank : NatAssign.Bank ports (loaded v first count) s.val:=by
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · rw [loaded_inside v first count i hi];exact g.ready.bank i hi
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl
      · simpa only [loaded,Function.update_of_ne (by decide : (500:ℕ)≠503),Function.update_self] using countWord
      · simpa only [loaded,Function.update_self] using firstWord
  have widths : ∀i∈ports,(loaded v first count i).bits.length≤B:=by
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · rw [loaded_inside v first count i hi];exact g.wordWidth i hi
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl
      · simpa only [loaded,Function.update_of_ne (by decide : (500:ℕ)≠503),Function.update_self] using hcount
      · simpa only [loaded,Function.update_self] using hfirst
  obtain ⟨cost,t,ex,hc,bt,zt,ft⟩:=NatAssign.executes ports (by
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · have h:=ids_ge i hi;omega
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hi;omega)
    plan valid (loaded v first count) input tape s bank g.ready.natural
  rw [changes] at ft
  rw [values v first count ((g.fixed 969 (by decide)).trans hthree)] at bt
  have bankt : NatAssign.Bank ids (prepared v first count) t.val:=by
    intro i hi
    have h:=bt i (Finset.mem_union_left _ hi)
    simpa only [loaded_inside _ first count i hi] using h
  have ready:=g.ready.stage bankt zt (ft.mono (by decide))
  have bound:=hc.trans (NatAssign.price_bound ports plan valid (loaded v first count) B widths
    (by simp [plan,NatAssign.Instruction.literalWidth]))
  refine ⟨cost,t,ex,?_,⟨ready,?_,?_,?_,?_⟩,ft⟩
  · change cost≤1536000*(B+2)^2 at bound
    exact bound.trans (by gcongr;norm_num)
  · intro i hi
    by_cases h0:i=989
    · subst i;simpa only [prepared,Function.update_self] using hcount
    · rw [prepared,Function.update_of_ne h0]
      by_cases h1:i=971
      · subst i;simpa only [Function.update_self] using hcursor
      · rw [Function.update_of_ne h1];exact g.wordWidth i hi
  · simpa only [ft.memory] using g.array
  · exact BankArray.word_of_eq (ft.tapes 962 (by decide)) g.clockWord
  · intro i hi
    have hi0 : i≠989 ∧ i≠971:=by simp only [fixedIds,Finset.mem_insert,Finset.mem_singleton] at hi;omega
    rw [prepared,Function.update_of_ne hi0.1,Function.update_of_ne hi0.2]
    exact g.fixed i hi

#print axioms prepare_executes
end Maxwell.Continuum.GeometryOutput.Readout
