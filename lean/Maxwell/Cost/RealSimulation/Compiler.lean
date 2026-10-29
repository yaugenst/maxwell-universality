import Maxwell.Cost.RealSimulation.Primitives
import Maxwell.Cost.RealSimulation.Encoding

namespace Maxwell.Cost.RealSimulation

open Control

/-- Simulator-owned scalar cells, disjoint from the caller's metadata and
the finite Boolean-register/tape-head frame. -/
def zeroRegister : ℕ := 9
def oneRegister : ℕ := 10
def activeRegister : ℕ := 11
def dispatchRegister : ℕ := 12
def coordinateRegister : ℕ := 13
def pointerRegister : ℕ := 14
def valueRegister : ℕ := 15

def sequence : List Code → Code
  | [] => .skip
  | [c] => c
  | c :: d :: cs => .seq c (sequence (d :: cs))

/-- The stride is fixed by the source program. It is computed by ordinary
index additions; there is no multiplication or address-conversion oracle. -/
def bankPointer (L : Layout) (bank coordinate : ℕ) : Code := sequence
  [literal pointerRegister bank,
   add pointerRegister pointerRegister workspaceOrigin,
   repeatAdd pointerRegister coordinate L.stride]

def incrementPC : Code := add virtualPC virtualPC oneRegister

def boundedInput (L : Layout) (dst coordinate : ℕ) : Code :=
  .branch inputLength coordinate (literal (L.bitRegister dst) 0)
    (.seq (bankPointer L L.inputBank coordinate)
      (load (L.bitRegister dst) pointerRegister))

/-- Only a sampled Boolean is converted from a real word to a natural word.
Both outcomes run five primitive instructions, including their explicit jump. -/
def drawBit (dst : ℕ) : Code := .call ⟨[
  .randomBit 0, .literal 1 0, .branchLE 0 1 3 5,
  .indexLiteral dst 0, .jump 7,
  .indexLiteral dst 1, .jump 7, .halt]⟩

/-- The decoder argument is itself finite structured machine code, with
the separately proved stack-decoding contract. It is not a state function. -/
def decodeStack (decoder : Code) : Code := sequence
  [copy 0 addressLength, copy 1 workspaceOrigin,
   add 1 1 oneRegister, copy 2 bankStride, decoder]

/-- Every source instruction is translated to finite ordinary instructions.
The decoder's loop is the only input-dependent extra work of random access. -/
def instruction (L : Layout) (decoder : Code) : BitRAMInstruction → Code
  | .literal r b => .seq (literal (L.bitRegister r) b.toNat) incrementPC
  | .bitXor dst left right => sequence
      [add valueRegister (L.bitRegister left) (L.bitRegister right),
       .branch valueRegister oneRegister
         (.branch oneRegister valueRegister (literal (L.bitRegister dst) 1)
           (literal (L.bitRegister dst) 0))
         (literal (L.bitRegister dst) 0), incrementPC]
  | .bitAnd dst left right => sequence
      [.branch (L.bitRegister left) zeroRegister (literal (L.bitRegister dst) 0)
        (copy (L.bitRegister dst) (L.bitRegister right)), incrementPC]
  | .bitNot dst src =>
      .seq (subtract (L.bitRegister dst) oneRegister (L.bitRegister src)) incrementPC
  | .readSequential dst => sequence
      [.branch headCenter inputHead
        (.seq (subtract coordinateRegister inputHead headCenter)
          (boundedInput L dst coordinateRegister))
        (literal (L.bitRegister dst) 0), incrementPC]
  | .inputLeft => .seq (subtract inputHead inputHead oneRegister) incrementPC
  | .inputRight => .seq (add inputHead inputHead oneRegister) incrementPC
  | .addressPeek dst => sequence
      [.branch addressLength zeroRegister (literal (L.bitRegister dst) 0)
        (sequence [subtract coordinateRegister addressLength oneRegister,
          bankPointer L 1 coordinateRegister, load (L.bitRegister dst) pointerRegister]),
       incrementPC]
  | .addressIsEmpty dst => sequence
      [.branch addressLength zeroRegister (literal (L.bitRegister dst) 1)
        (literal (L.bitRegister dst) 0), incrementPC]
  | .readTape t dst present => sequence
      [bankPointer L (2 + t) (L.tapeHead t), load valueRegister pointerRegister,
       subtract (L.bitRegister dst) valueRegister oneRegister,
       .branch valueRegister zeroRegister (literal (L.bitRegister present) 0)
         (literal (L.bitRegister present) 1), incrementPC]
  | .writeTape t src => sequence
      [add valueRegister (L.bitRegister src) oneRegister,
       bankPointer L (2 + t) (L.tapeHead t), save pointerRegister valueRegister,
       incrementPC]
  | .eraseTape t => sequence
      [bankPointer L (2 + t) (L.tapeHead t), save pointerRegister zeroRegister,
       incrementPC]
  | .tapeLeft t => .seq (subtract (L.tapeHead t) (L.tapeHead t) oneRegister) incrementPC
  | .tapeRight t => .seq (add (L.tapeHead t) (L.tapeHead t) oneRegister) incrementPC
  | .addressPush src => sequence
      [bankPointer L 1 addressLength, save pointerRegister (L.bitRegister src),
       add addressLength addressLength oneRegister, incrementPC]
  | .addressPop => .seq (subtract addressLength addressLength oneRegister) incrementPC
  | .addressClear => .seq (literal addressLength 0) incrementPC
  | .readInput dst => sequence
      [decodeStack decoder, boundedInput L dst 3, incrementPC]
  | .readMemory dst => sequence
      [decodeStack decoder, bankPointer L 0 3, load (L.bitRegister dst) pointerRegister,
       incrementPC]
  | .writeMemory src => sequence
      [decodeStack decoder, bankPointer L 0 3, save pointerRegister (L.bitRegister src),
       incrementPC]
  | .branch r yes no =>
      .branch (L.bitRegister r) zeroRegister (literal virtualPC no) (literal virtualPC yes)
  | .jump pc => literal virtualPC pc
  | .randomBit r => .seq (drawBit (L.bitRegister r)) incrementPC
  | .output r => sequence
      [bankPointer L L.outputBank outputLength, save pointerRegister (L.bitRegister r),
       add outputLength outputLength oneRegister, incrementPC]
  | .halt => literal activeRegister 0

/-- A literal finite dispatch chain. Invalid source PCs reach an ordinary
halt path, exactly as in the source machine. -/
def dispatch (L : Layout) (decoder : Code) : ℕ → List BitRAMInstruction → Code
  | _, [] => literal activeRegister 0
  | i, op :: rest => .seq (literal dispatchRegister i)
      (.branch virtualPC dispatchRegister
        (.branch dispatchRegister virtualPC (instruction L decoder op)
          (literal activeRegister 0))
        (dispatch L decoder (i + 1) rest))

def interpreter (L : Layout) (decoder : Code) (M : BitRAM) : Code :=
  .loop oneRegister activeRegister (dispatch L decoder 0 M.code)

/-- The finite initialization prefix clears exactly the fixed source frame.
Dynamic memory/tape freshness is an explicit entry condition. -/
def initializeState (L : Layout) : Code := sequence
  ([literal zeroRegister 0, literal oneRegister 1, literal activeRegister 1,
    literal virtualPC 0, literal addressLength 0, literal outputLength 0,
    copy inputHead headCenter] ++
   (List.range L.registerCount).map (fun r => literal (L.bitRegister r) 0) ++
   (List.range L.tapeCount).map (fun t => copy (L.tapeHead t) headCenter))

def compiled (L : Layout) (decoder : Code) (M : BitRAM) : Machine :=
  (Code.seq (initializeState L) (interpreter L decoder M)).compile

end Maxwell.Cost.RealSimulation
