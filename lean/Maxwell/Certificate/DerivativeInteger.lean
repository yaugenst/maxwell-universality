import Maxwell.Certificate.IntegerAction

namespace Maxwell.Certificate.DerivativeBinding
open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Direction)
open Maxwell.Certificate.PrimitiveBinding

def blockAction {R : Type*} [Sub R] (D : Direction → (Cell → R) → Cell → R)
    (v : Electric → R) (e : Electric) : R :=
  if e.1 = 0 then D 1 (fun p => v (2,p)) e.2 - D 2 (fun p => v (1,p)) e.2
  else if e.1 = 1 then D 2 (fun p => v (0,p)) e.2 - D 0 (fun p => v (2,p)) e.2
  else D 0 (fun p => v (1,p)) e.2 - D 1 (fun p => v (0,p)) e.2

def blockTransposeAction {R : Type*} [Sub R] (D : Direction → (Cell → R) → Cell → R)
    (v : Electric → R) (e : Electric) : R :=
  if e.1 = 0 then D 2 (fun p => v (1,p)) e.2 - D 1 (fun p => v (2,p)) e.2
  else if e.1 = 1 then D 0 (fun p => v (2,p)) e.2 - D 2 (fun p => v (0,p)) e.2
  else D 1 (fun p => v (0,p)) e.2 - D 0 (fun p => v (1,p)) e.2

def firstActionI (k : Translation) (j : Direction) (v : Cell → ℤ) (p : Cell) : ℤ :=
  differenceActionI k j v p + 2 * v p

def firstTransposeActionI (k : Translation) (j : Direction) (v : Cell → ℤ) (p : Cell) : ℤ :=
  differenceTransposeActionI k j v p + 2 * v p

def KActionI (k : Translation) (i : Direction) (v : Electric → ℤ) : Electric → ℤ :=
  blockAction (fun j v p => if j = i then firstActionI k i v p else 0) v

def KTransposeActionI (k : Translation) (i : Direction) (v : Electric → ℤ) : Electric → ℤ :=
  blockTransposeAction (fun j v p => if j = i then firstTransposeActionI k i v p else 0) v

def LActionI (k : Translation) (i : Direction) (v : Electric → ℤ) : Electric → ℤ :=
  blockAction (fun j v p => if j = i then differenceActionI k i v p else 0) v

def LTransposeActionI (k : Translation) (i : Direction) (v : Electric → ℤ) : Electric → ℤ :=
  blockTransposeAction (fun j v p => if j = i then differenceTransposeActionI k i v p else 0) v

def BActionI (k : Translation) (i : Direction) (v : Electric → ℤ) (e : Electric) : ℤ :=
  curlTransposeActionI k (KActionI k i v) e - KTransposeActionI k i (curlActionI k v) e

def DActionI (k : Translation) (i j : Direction) (v : Electric → ℤ) (e : Electric) : ℤ :=
  KTransposeActionI k i (KActionI k j v) e + KTransposeActionI k j (KActionI k i v) e -
    if i = j then LTransposeActionI k i (curlActionI k v) e +
      curlTransposeActionI k (LActionI k i v) e else 0

end Maxwell.Certificate.DerivativeBinding
