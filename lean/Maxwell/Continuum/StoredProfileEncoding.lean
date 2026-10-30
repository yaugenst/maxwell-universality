import Maxwell.Continuum.StoredDyadicArray
import Maxwell.Continuum.StoredPlacementEncoding
import Maxwell.Continuum.ProfileCoefficientBits

/-! The raw dyadic table serializer emits the exact existing radial-profile
format, including its shared precision and corrected coefficient order. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost

theorem profile_arrayBits (N : ℕ) :
    StoredDyadic.arrayBits (encodedCoefficient N) (profileDegree N)=profileBits N := by
  unfold StoredDyadic.arrayBits StoredDyadic.stream profileBits Codec.list profileData
  rw [List.length_ofFn,List.ofFn_eq_map,List.flatMap_map,
    StoredPlacement.range_flatMap_finRange]
  exact List.append_assoc ..

#print axioms profile_arrayBits
end Maxwell.Continuum.Profile.Runtime
