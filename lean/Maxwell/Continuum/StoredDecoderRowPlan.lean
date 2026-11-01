import Maxwell.Cost.Structured.NatAssign.Bounds
import Maxwell.Cost.Structured.NatAssign.Values

/-! A decoder row is calculated from the packed coordinate triple, the
stored chronological well numerator, and the runtime decoder metadata. -/
namespace Maxwell.Continuum.DecoderRow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 2500000

def inputs : Finset ℕ:={144,976,977,978,982,983,984,985,1000,4705,4706,4707,4708}
def outputs : Finset ℕ:={228,229,4800,4803,4804,4805,4806,4807}
def ids : Finset ℕ:=inputs∪outputs

def plan : List NatAssign.Instruction :=
  [.literal 4806 2,
   .copy 976 4803,.multiply 4806 4803,.multiply 983 4803,.add 982 4803,
   .copy 977 4804,.multiply 4806 4804,.multiply 984 4804,.add 982 4804,
   .copy 978 4805,.multiply 4806 4805,.multiply 985 4805,.add 982 4805,
   .copy 4804 4800,.multiply 4706 4800,.add 4805 4800,
   .copy 4705 4807,.multiply 4706 4807,.multiply 4803 4807,.add 4807 4800,
   .copy 1000 228,.multiply 4707 228,.copy 144 229,.multiply 4708 229]

def values (v : ℕ→ℕ):=NatAssign.values plan v
def coordinate (v : ℕ→ℕ) (j : Fin 3):=v 982+v (983+j.val)*(2*v (976+j.val))
def address (v : ℕ→ℕ):=coordinate v 2+v 4706*coordinate v 1+
  (v 4705*v 4706)*coordinate v 0

theorem lower : ∀i∈ids,4 ≤ i:=by
  simp only [ids,inputs,outputs,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton];omega
theorem valid : ∀a∈plan,a.Valid ids:=by
  simp [plan,NatAssign.Instruction.Valid,ids,inputs,outputs]
theorem literals : ∀a∈plan,a.literalWidth≤2:=by
  simp [plan,NatAssign.Instruction.literalWidth]
  decide

theorem result (v : ℕ→ℕ):
    values v 4800=address v ∧ values v 228=v 1000*v 4707 ∧
      values v 229=v 144*v 4708:=by
  simp only [values,plan,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,Function.update_apply]
  norm_num
  unfold address coordinate
  norm_num
  constructor
  · ring
  · constructor <;> ring

theorem kept (v : ℕ→ℕ) (i : ℕ) (hi : i∉outputs) : values v i=v i:=by
  apply NatAssign.values_preserves
  intro a ha
  have targets : ∀a∈plan,a.target∈outputs:=by
    simp [plan,outputs,NatAssign.Instruction.target]
  have mem := targets a ha
  exact fun he=>hi (he.symm ▸ mem)

def width (B : ℕ):=2^plan.length*(B+1)
def costBound (B : ℕ):=3000*8^plan.length*(B+2)^2

theorem executes (v : ℕ→ℕ) (B : ℕ) (hB : 2≤B)
    (bound : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val):
    ∃cost t,Executes input tape (NatAssign.code plan) cost s t ∧cost≤costBound B ∧
      NatAssign.Bank ids (values v) t.val ∧NatAssign.Scratch t.val ∧
      (∀i∈ids,(values v i).bits.length≤width B) ∧
      BinaryPrecision.Frame ({0,1,2,3}∪outputs) s.val t.val:=by
  obtain ⟨cost,t,ex,hc,bt,st,ft⟩:=NatAssign.executes ids lower plan valid v input tape s bank scratch
  refine ⟨cost,t,ex,hc.trans (NatAssign.price_bound ids plan valid v B bound
    (fun a ha=>(literals a ha).trans hB)),bt,st,?_,ft.mono (by decide)⟩
  intro i hi
  have hh:=NatAssign.values_width ids plan valid v B bound
    (fun a ha=>(literals a ha).trans hB) i hi
  change (values v i).bits.length+1≤width B at hh
  omega

#print axioms executes
end Maxwell.Continuum.DecoderRow
