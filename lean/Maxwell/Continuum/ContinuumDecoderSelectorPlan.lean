import Maxwell.Cost.Structured.NatAssign.Clog

/-! Runtime natural metadata for the continuum singleton decoder. Every
operand is a retained source or selected-parameter word. -/
namespace Maxwell.Continuum.DecoderSelectors
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

def inputs : Finset ℕ:={501,504,505,506,507,2221,2237,2240,2241,2242,2244,2245,4428}
def outputs : Finset ℕ:={4700,4701,4702,4703,4704,4705,4706,4707,4708,4710,4712,4713,4714}
def ids : Finset ℕ:=inputs∪outputs

def plan : List NatAssign.Instruction :=
  [.copy 501 4700,.multiply 501 4700,.multiply 2245 4700,.multiply 2237 4700,
   .literal 4712 512,.multiply 4712 4700,
   .copy 2221 4712,.multiply 2244 4712,.add 2221 4712,.literal 4713 4,.add 4713 4712,
   .literal 4713 2,.literal 4714 1,
   .copy 2240 4704,.add 4712 4704,.multiply 4713 4704,.add 4714 4704,
   .copy 2241 4705,.add 4712 4705,.multiply 4713 4705,.add 4714 4705,
   .copy 2242 4706,.add 4712 4706,.multiply 4713 4706,.add 4714 4706,
   .copy 4704 4703,.multiply 4705 4703,.multiply 4706 4703,
   .copy 506 4707,.multiply 505 4707,.copy 507 4708,.multiply 504 4708,.copy 4428 4702]

def value (v : ℕ→ℕ):=NatAssign.values plan v

def code : Code:=.seq (NatAssign.code plan)
  (.seq (NatAssign.clogCode 4700 4710 4701) (NatAssign.code [.add 4713 4701]))

def result (v : ℕ→ℕ):=NatAssign.values [.add 4713 4701] (NatAssign.clogValues (value v) 4700 4710 4701)

theorem ids_lower : ∀i∈ids,4 ≤ i:=by simp only [ids,inputs,outputs,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton];omega
theorem valid : ∀a∈plan,a.Valid ids:=by simp [plan,NatAssign.Instruction.Valid,ids,inputs,outputs]
theorem literals : ∀a∈plan,a.literalWidth≤10:=by
  simp [plan,NatAssign.Instruction.literalWidth]
  decide

theorem values (v : ℕ→ℕ) :
    value v 4700=512*(v 501)^2*v 2245*v 2237 ∧ value v 4713=2 ∧
    value v 4702=v 4428 ∧
    value v 4704=2*(v 2240+v 2221+v 2221*v 2244+4)+1 ∧
    value v 4705=2*(v 2241+v 2221+v 2221*v 2244+4)+1 ∧
    value v 4706=2*(v 2242+v 2221+v 2221*v 2244+4)+1 ∧
    value v 4703=value v 4704*(value v 4705*value v 4706) ∧
    value v 4707=v 506*v 505 ∧ value v 4708=v 507*v 504:=by
  simp only [value,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target]
  simp only [Function.update_apply]
  norm_num
  repeat' constructor
  all_goals ring

theorem result_log (v : ℕ→ℕ) : result v 4701=Nat.clog 2 (512*(v 501)^2*v 2245*v 2237)+2:=by
  simp only [result,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target,Function.update_self,NatAssign.clogValues,
    Function.update_of_ne (by decide : (4713:ℕ)≠4701),Function.update_of_ne (by decide : (4713:ℕ)≠4710)]
  rw [(values v).1,(values v).2.1,Nat.add_comm]

theorem result_kept (v : ℕ→ℕ) (i : ℕ) (h0 : i≠4701) (h1 : i≠4710) : result v i=value v i:=by
  simp only [result,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.clogValues,Function.update_of_ne h0,Function.update_of_ne h1]

end Maxwell.Continuum.DecoderSelectors
