import Maxwell.Continuum.Main

/-! Type-check the final continuum contract without claiming an inhabitant.
The eventual theorem must have this exact type, with no execution premises. -/
#check Maxwell.Continuum.Realization.Encodes
#check Maxwell.Continuum.Realization.Decodes
#check Maxwell.Continuum.Realization.Resources
#check Maxwell.Continuum.Realization.GoodDraw
#check Maxwell.Continuum.Realization.QuantitativeRealization

example (p : Maxwell.Source.Parameters) : Prop :=
  Maxwell.Continuum.Realization.QuantitativeRealization p
