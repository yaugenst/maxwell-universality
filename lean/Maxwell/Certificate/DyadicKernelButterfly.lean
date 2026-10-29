import Maxwell.Certificate.DyadicKernelFFTStrict

namespace Maxwell.Certificate.DyadicKernel.Butterfly

abbrev Values := Array Rectangle

def get (a : Values) (i : Nat) : Rectangle := a[i]?.getD zero

def build {n : Nat} (f : Fin n → Rectangle) : Values :=
  FFT.collect (fun i k => FFT.forceRectangle (f i) k) (List.ofFn fun i : Fin n => i)
    (fun xs => ⟨xs⟩)

def even (n : Nat) (a : Values) : Values :=
  Array.ofFn fun i : Fin n => get a (2*i.val)

def odd (n : Nat) (a : Values) : Values :=
  Array.ofFn fun i : Fin n => get a (2*i.val+1)

def five (root : Int → Rectangle) (stride : Int) (input : Values) : Values :=
  build fun k : Fin 5 => dotRound 52 (List.ofFn fun j : Fin 5 =>
    (get input j.val,root (stride*k.val*j.val)))

def unit52 : Rectangle := ⟨2^52,0,0⟩

def pair (root : Int → Rectangle) (phase : Int) (upper : Bool)
    (ev od : Rectangle) : Rectangle :=
  dotRound 52 [(ev,unit52),(if upper then neg od else od,root phase)]

def combine (n : Nat) (root : Int → Rectangle) (stride : Int)
    (ev od : Values) : Values :=
  build fun k : Fin (n*2) =>
    let j := if k.val < n then k.val else k.val-n
    pair root (stride*j) (decide (n ≤ k.val)) (get ev j) (get od j)

structure Ten where
  even5 : Values
  odd5 : Values
  result : Values

def ten (root : Int → Rectangle) (sign : Int) (input : Values) : Ten :=
  let ev := five root (4*sign) (even 5 input)
  let od := five root (4*sign) (odd 5 input)
  ⟨ev,od,combine 5 root (2*sign) ev od⟩

structure Twenty where
  even10 : Ten
  odd10 : Ten
  result : Values

def twenty (root : Int → Rectangle) (sign : Int) (input : Values) : Twenty :=
  let ev := ten root sign (even 10 input)
  let od := ten root sign (odd 10 input)
  ⟨ev,od,combine 10 root sign ev.result od.result⟩

def normalize (n : Nat) (norm : Rectangle) (input : Values) : Values :=
  build fun i : Fin n => mulRound 52 (get input i.val) norm

def transform10 (root : Int → Rectangle) (norm : Rectangle) (sign : Int)
    (input : Values) : Values := normalize 10 norm (ten root sign input).result

def transform20 (root : Int → Rectangle) (norm : Rectangle) (sign : Int)
    (input : Values) : Values := normalize 20 norm (twenty root sign input).result

end Maxwell.Certificate.DyadicKernel.Butterfly
