import Maxwell.Certificate.IntegerAction

namespace Maxwell.Certificate.PrimitiveBinding
open Maxwell.Spectral.PrimitiveYee

/-- The exact staggered electric inversion, including the primitive boundary sign. -/
def electricInversionActionI (k : Translation) (v : Electric → ℤ) (e : Electric) : ℤ :=
  let r := -representative e.2 - rawUnit e.1;
  -(if Even (∑ a, k a * reduceTranslation r a) then 1 else -1) *
    v (e.1, reduceCell r)

end Maxwell.Certificate.PrimitiveBinding
