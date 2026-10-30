import Maxwell.Cost.Structured.Correctness
import Maxwell.Cost.SourceCircuit.Archive

/-! A fixed finite compiler redirects the write-only output stream to a
reserved tape. Every original instruction occupies two literal code slots;
the second slot is an ordinary jump or the captured bit's head advance. -/
namespace Maxwell.Continuum.OutputCapture
open Maxwell.Cost Maxwell.Cost.Structured

def avoids (archive : ℕ) : BitRAMInstruction → Bool
  | .readTape t _ _ | .writeTape t _ | .eraseTape t | .tapeLeft t | .tapeRight t =>
    decide (t ≠ archive)
  | _ => true

def first (archive : ℕ) : BitRAMInstruction → BitRAMInstruction
  | .branch r yes no => .branch r (2*yes) (2*no)
  | .jump target => .jump (2*target)
  | .output r => .writeTape archive r
  | i => i

def second (archive pc : ℕ) : BitRAMInstruction → BitRAMInstruction
  | .output _ => .tapeRight archive
  | _ => .jump (2*(pc+1))

def program (archive : ℕ) (body : BitRAM) : BitRAM := ⟨List.ofFn
  (fun i : Fin (2*body.code.length) =>
    let instruction := body.code[i.val/2]'(by omega)
    if i.val%2=0 then first archive instruction
    else second archive (i.val/2) instruction)⟩

@[simp] theorem program_length (archive : ℕ) (body : BitRAM) :
    (program archive body).code.length=2*body.code.length := by
  simp [program]

theorem lookup_first (archive : ℕ) (body : BitRAM) (pc : ℕ)
    (i : BitRAMInstruction) (hi : body.code[pc]?=some i) :
    (program archive body).code[2*pc]?=some (first archive i) := by
  have hp : pc<body.code.length := List.getElem?_eq_some_iff.mp hi |>.1
  have hv : body.code[pc]'hp=i := by simpa using List.getElem?_eq_some_iff.mp hi |>.2
  simp [program,show 2*pc<2*body.code.length by omega,hv]

theorem lookup_second (archive : ℕ) (body : BitRAM) (pc : ℕ)
    (i : BitRAMInstruction) (hi : body.code[pc]?=some i) :
    (program archive body).code[2*pc+1]?=some (second archive pc i) := by
  have hp : pc<body.code.length := List.getElem?_eq_some_iff.mp hi |>.1
  have hv : body.code[pc]'hp=i := by simpa using List.getElem?_eq_some_iff.mp hi |>.2
  have hd : (2*pc+1)/2=pc := by omega
  have hm : (2*pc+1)%2=1 := by omega
  simp [program,show 2*pc+1<2*body.code.length by omega,hd,hm,hv]

def state (archive : ℕ) (output accumulated : List Bool) (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 2*s.pc
    output := output
    tapes := Function.update s.tapes archive (BitTape.atEnd accumulated)}

theorem initial_state (archive : ℕ) (accumulated : List Bool) (s : Store)
    (ha : s.val.tapes archive=BitTape.atEnd accumulated) :
    state archive s.val.output accumulated s.val=s.val := by
  have ht : Function.update s.val.tapes archive (BitTape.atEnd accumulated)=s.val.tapes := by
    rw [← ha]; exact Function.update_eq_self archive s.val.tapes
  have hp : 2*s.val.pc=s.val.pc := by rw [s.property]
  simp only [state,hp,ht]

end Maxwell.Continuum.OutputCapture
