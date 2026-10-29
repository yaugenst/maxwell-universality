import Maxwell.Certificate.DyadicKernelRounded

namespace Maxwell.Certificate.DyadicKernel

def Triple.get (a : Triple) (i : Fin 3) : Rectangle :=
  match i.val with
  | 0 => a.x
  | 1 => a.y
  | _ => a.z

def Triple.ofFn (a : Fin 3 → Rectangle) : Triple := ⟨a 0,a 1,a 2⟩

def dotTriple (p : Nat) (a b : Triple) : Rectangle :=
  dotRound p [(a.x,b.x),(a.y,b.y),(a.z,b.z)]

def laplacianRound (p : Nat) (d : Triple) : Rectangle :=
  dotRound p [(conjugate d.x,d.x),(conjugate d.y,d.y),(conjugate d.z,d.z)]

def projectRound (p : Nat) (d raw : Triple) (lap : Rectangle) : Option Triple := do
  let quotient ← divRound p (dotTriple p d raw) lap
  return Triple.ofFn fun i => add (raw.get i) (neg (mulRound p (conjugate (d.get i)) quotient))

def curlRow (d : Triple) (i : Fin 3) : Triple :=
  match i.val with
  | 0 => ⟨zero,neg d.z,d.y⟩
  | 1 => ⟨d.z,zero,neg d.x⟩
  | _ => ⟨neg d.y,d.x,zero⟩

def curlRound (p : Nat) (adjoint : Bool) (d u : Triple) : Triple :=
  Triple.ofFn fun i => dotRound p (List.ofFn fun j : Fin 3 =>
    ((if adjoint then conjugate ((curlRow d j).get i) else (curlRow d i).get j),u.get j))

def divideTriple (p : Nat) (u denominators : Triple) : Option Triple := do
  let x ← divRound p u.x denominators.x
  let y ← divRound p u.y denominators.y
  let z ← divRound p u.z denominators.z
  return ⟨x,y,z⟩

def magneticRound (d weighted field : Triple) : Triple :=
  Triple.ofFn fun i => dotRound 52
    ((⟨-(2^46),0,0⟩,field.get i) ::
      List.ofFn fun j : Fin 3 => ((curlRow d i).get j,weighted.get j))

end Maxwell.Certificate.DyadicKernel
