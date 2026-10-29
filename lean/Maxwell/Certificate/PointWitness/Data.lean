import Maxwell.Certificate.PointWitness.Numerator0

import Maxwell.Certificate.PointWitness.Imagenumerator0

import Maxwell.Certificate.PointWitness.Numerator1

import Maxwell.Certificate.PointWitness.Imagenumerator1

namespace Maxwell.Certificate.PointWitness

open Maxwell.Spectral.PrimitiveYee

def momentum : Translation := ![1,1,0]

noncomputable def vector0 (e : Electric) : ℚ := (numerator0 e : ℚ) / 2^101

noncomputable def image0 (e : Electric) : ℚ := (imageNumerator0 e : ℚ) / 2^130

end Maxwell.Certificate.PointWitness
