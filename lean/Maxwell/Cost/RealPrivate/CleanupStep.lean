import Maxwell.Cost.RealPrivate.Frame

namespace Maxwell.Cost.RealPrivate.Cleanup
open RealSimulation.Control

def body : Code := block
  [subtract 10 9 oneRegister, bankPointer 2 10, load coordinateRegister pointerRegister,
   bankPointer 0 coordinateRegister, realStore pointerRegister 3,
   save pointerRegister zeroRegister, add 9 9 oneRegister]

noncomputable def stepState (s : Store) (origin index address : ℕ) : Store :=
  let a := ((s.put 10 index).put pointerRegister (slot origin 2 index)).put coordinateRegister address
  let b := a.put pointerRegister (slot origin 0 address)
  ((putWord b (slot origin 0 address) 0).put (slot origin 0 address) 0).put 9 (index+2)

theorem step_executes (input : RAMInput) (tape : ℕ→Bool) (s : Store)
    (origin index address : ℕ) (high : 256≤origin)
    (horigin : s.val.indices originRegister=origin) (hzero : s.val.indices zeroRegister=0)
    (hone : s.val.indices oneRegister=1) (hcursor : s.val.indices 9=index+1)
    (hreal : s.val.words 3=0) (hlog : s.val.indices (slot origin 2 index)=address) :
    Executes input tape body 36 s (stepState s origin index address) := by
  have h160 : s.val.indices 160=origin := horigin
  have h6 : s.val.indices 6=0 := hzero
  have h7 : s.val.indices 7=1 := hone
  let a := s.put 10 index
  let b := a.put pointerRegister (slot origin 2 index)
  let c := b.put coordinateRegister address
  let d := c.put pointerRegister (slot origin 0 address)
  let e := putWord d (slot origin 0 address) 0
  let f := e.put (slot origin 0 address) 0
  have hn (bank a j : ℕ) (hj : j<256) : slot origin bank a≠j := slot_ne_small high bank a j hj
  have hnr (bank a j : ℕ) (hj : j<256) : j≠slot origin bank a := (hn bank a j hj).symm
  have ea : Executes input tape (subtract 10 9 oneRegister) 2 s a := by
    simpa [a,hone,hcursor] using subtract_executes input tape s 10 9 oneRegister
  have eb : Executes input tape (bankPointer 2 10) 13 a b := by
    simpa [a,b,originRegister,pointerRegister,h160] using
      bankPointer_executes input tape a 2 10 (by decide)
  have ec : Executes input tape (load coordinateRegister pointerRegister) 2 b c := by
    simpa [b,a,c,hn,pointerRegister,hlog] using load_executes input tape b coordinateRegister pointerRegister
  have ed : Executes input tape (bankPointer 0 coordinateRegister) 13 c d := by
    simpa [c,b,a,d,originRegister,coordinateRegister,pointerRegister,h160] using
      bankPointer_executes input tape c 0 coordinateRegister (by decide)
  have ee : Executes input tape (realStore pointerRegister 3) 2 d e := by
    simpa [e,d,c,b,a,Store.put,hreal,pointerRegister] using realStore_executes input tape d pointerRegister 3
  have ef : Executes input tape (save pointerRegister zeroRegister) 2 e f := by
    simpa [f,e,d,c,b,a,putWord,zeroRegister,coordinateRegister,pointerRegister,h6] using
      save_executes input tape e pointerRegister zeroRegister
  have eg : Executes input tape (add 9 9 oneRegister) 2 f (stepState s origin index address) := by
    simpa [stepState,f,e,d,c,b,a,putWord,hnr,oneRegister,coordinateRegister,pointerRegister,h7,hcursor,
      Nat.add_assoc] using add_executes input tape f 9 9 oneRegister
  exact ea.seq (eb.seq (ec.seq (ed.seq (ee.seq (ef.seq eg)))))

end Maxwell.Cost.RealPrivate.Cleanup
