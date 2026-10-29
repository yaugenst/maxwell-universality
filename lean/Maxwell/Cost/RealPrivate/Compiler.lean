import Maxwell.Cost.RealPrivate.Layout
import Maxwell.Cost.RealSimulation.Compiler

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

def block := RealSimulation.sequence

def realLiteral (dst : ℕ) (q : ℚ) : Code := .call ⟨[.literal dst q, .halt]⟩
def realLoad (dst address : ℕ) : Code := .call ⟨[.load dst address, .halt]⟩
def realStore (address src : ℕ) : Code := .call ⟨[.store address src, .halt]⟩
def realAdd (dst left right : ℕ) : Code := .call ⟨[.add dst left right, .halt]⟩
def realMultiply (dst left right : ℕ) : Code := .call ⟨[.multiply dst left right, .halt]⟩
def realDivide (dst left right : ℕ) : Code := .call ⟨[.divide dst left right, .halt]⟩
def randomBit (dst : ℕ) : Code := .call ⟨[.randomBit dst, .halt]⟩

def staticPointer (bank address : ℕ) : Code :=
  .seq (literal pointerRegister (4 * address + bank))
    (add pointerRegister pointerRegister originRegister)

def bankPointer (bank coordinate : ℕ) : Code := block
  [literal pointerRegister bank, add pointerRegister pointerRegister originRegister,
   repeatAdd pointerRegister coordinate 4]

def inputPointer (base stride coordinate : ℕ) : Code :=
  .seq (copy pointerRegister base) (repeatAdd pointerRegister coordinate stride)

def getIndex (address dst : ℕ) : Code :=
  .seq (staticPointer 0 address) (load dst pointerRegister)
def getWord (address dst : ℕ) : Code :=
  .seq (staticPointer 0 address) (realLoad dst pointerRegister)

/-- A finite log records every logical source address whose real or index
cell was written. Cleanup can restore both types at those addresses. -/
def appendLog : Code := block
  [bankPointer 2 logLength, save pointerRegister coordinateRegister,
   add logLength logLength oneRegister]

def setIndex (address src : ℕ) : Code := block
  [staticPointer 0 address, save pointerRegister src,
   literal coordinateRegister address, appendLog]
def setWord (address src : ℕ) : Code := block
  [staticPointer 0 address, realStore pointerRegister src,
   literal coordinateRegister address, appendLog]

def incrementPC : Code := add sourcePC sourcePC oneRegister

def readIndexInput (L : Layout) : Code :=
  .branch indexInputLength coordinateRegister (literal valueRegister 0)
    (.seq (inputPointer indexInputBase L.indexInputStride coordinateRegister)
      (load valueRegister pointerRegister))

def readRealInput (L : Layout) : Code :=
  .branch realInputLength coordinateRegister (realLiteral 0 0)
    (.seq (inputPointer realInputBase L.realInputStride coordinateRegister)
      (realLoad 0 pointerRegister))

/-- A real comparison branches through an ordinary literal six-instruction
program. Neither outcome is converted by a real-to-natural primitive. -/
def realBranch (yes no : ℕ) : Code := .call ⟨[
  .branchLE 0 1 1 3, .indexLiteral sourcePC yes, .jump 5,
  .indexLiteral sourcePC no, .jump 5, .halt]⟩

def finished : Code := .seq (literal statusRegister 1) (literal activeRegister 0)

/-- All source registers, including indirectly addressed cells, are mapped
through the same private bank. Input reads use already-produced caller
buffers and outputs use separate banks; external RAMInput is unchanged. -/
def instruction (L : Layout) : RAMInstruction → Code
  | .literal dst q => block [realLiteral 0 q, setWord dst 0, incrementPC]
  | .copy dst src => block [getWord src 0, setWord dst 0, incrementPC]
  | .add dst left right => block
      [getWord left 0, getWord right 1, realAdd 2 0 1, setWord dst 2, incrementPC]
  | .multiply dst left right => block
      [getWord left 0, getWord right 1, realMultiply 2 0 1, setWord dst 2, incrementPC]
  | .divide dst left right => block
      [getWord left 0, getWord right 1, realDivide 2 0 1, setWord dst 2, incrementPC]
  | .input dst address => block
      [getIndex address coordinateRegister, readRealInput L, setWord dst 0, incrementPC]
  | .inputIndex dst address => block
      [getIndex address coordinateRegister, readIndexInput L, setIndex dst valueRegister, incrementPC]
  | .load dst address => block
      [getIndex address coordinateRegister, bankPointer 0 coordinateRegister,
       realLoad 0 pointerRegister, setWord dst 0, incrementPC]
  | .store address src => block
      [getIndex address coordinateRegister, getWord src 0, bankPointer 0 coordinateRegister,
       realStore pointerRegister 0, appendLog, incrementPC]
  | .loadIndex dst address => block
      [getIndex address coordinateRegister, bankPointer 0 coordinateRegister,
       load valueRegister pointerRegister, setIndex dst valueRegister, incrementPC]
  | .storeIndex address src => block
      [getIndex address coordinateRegister, getIndex src valueRegister,
       bankPointer 0 coordinateRegister, save pointerRegister valueRegister,
       appendLog, incrementPC]
  | .indexLiteral dst value => block [literal valueRegister value, setIndex dst valueRegister, incrementPC]
  | .indexCopy dst src => block [getIndex src valueRegister, setIndex dst valueRegister, incrementPC]
  | .indexAdd dst left right => block
      [getIndex left leftRegister, getIndex right rightRegister,
       add valueRegister leftRegister rightRegister, setIndex dst valueRegister, incrementPC]
  | .indexSubtract dst left right => block
      [getIndex left leftRegister, getIndex right rightRegister,
       subtract valueRegister leftRegister rightRegister, setIndex dst valueRegister, incrementPC]
  | .branchLE left right yes no => block [getWord left 0, getWord right 1, realBranch yes no]
  | .branchIndexLE left right yes no => block
      [getIndex left leftRegister, getIndex right rightRegister,
       .branch leftRegister rightRegister (literal sourcePC yes) (literal sourcePC no)]
  | .jump target => literal sourcePC target
  | .randomBit dst => block [randomBit 0, setWord dst 0, incrementPC]
  | .output src => block
      [getWord src 0, bankPointer 1 realOutputLength, realStore pointerRegister 0,
       add realOutputLength realOutputLength oneRegister, incrementPC]
  | .outputIndex src => block
      [getIndex src valueRegister, bankPointer 1 indexOutputLength, save pointerRegister valueRegister,
       add indexOutputLength indexOutputLength oneRegister, incrementPC]
  | .halt => finished

def dispatch (L : Layout) : ℕ → List RAMInstruction → Code
  | _, [] => finished
  | i, op :: rest => .seq (literal dispatchRegister i)
      (.branch sourcePC dispatchRegister
        (.branch dispatchRegister sourcePC (instruction L op) finished)
        (dispatch L (i + 1) rest))

/-- Fuel is decremented by actual code, including the charged observation
of a halt. Exhaustion always returns status0 without executing another
source instruction, on every input and every random tape. -/
def cappedInterpreter (L : Layout) (M : Machine) : Code :=
  .loop oneRegister activeRegister
    (.branch oneRegister fuelRegister
      (.seq (subtract fuelRegister fuelRegister oneRegister) (dispatch L 0 M.code))
      (literal activeRegister 0))

def initializeState : Code := block
  [literal zeroRegister 0, literal oneRegister 1, literal statusRegister 0,
   literal realOutputLength 0, literal indexOutputLength 0, literal logLength 0,
   literal sourcePC 0, literal activeRegister 1]

def program (L : Layout) (M : Machine) : Machine :=
  (Code.seq initializeState (cappedInterpreter L M)).compile

/-- The log cursor is one-based. Clearing both typed cells at every recorded
address safely handles aliases and repeated writes. -/
def cleanup : Code := block
  [literal 9 1, realLiteral 3 0,
   .loop 9 logLength (block
     [subtract 10 9 oneRegister, bankPointer 2 10, load coordinateRegister pointerRegister,
      bankPointer 0 coordinateRegister, realStore pointerRegister 3,
      save pointerRegister zeroRegister, add 9 9 oneRegister])]

end Maxwell.Cost.RealPrivate
