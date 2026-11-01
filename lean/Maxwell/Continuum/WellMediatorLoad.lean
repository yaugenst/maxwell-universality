import Maxwell.Continuum.RationalDataflowNaturalLoad
import Maxwell.Continuum.WellStrengthReset

/-! The axis tests consume four words copied from the two actual stored
geometry points. No geometric direction is supplied to the program. -/
namespace Maxwell.Continuum.RationalDataflow.WellMediatorLoad
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000

def plan : List NaturalChannel.Load.Assignment := [(976,8),(979,9),(977,10),(980,11)]
def code : Code := NaturalChannel.Load.code plan
def values (geometry : ℕ→ℕ) (v : ℕ→Parts) : ℕ→Parts := NaturalChannel.Load.values plan geometry v

theorem valid : NaturalChannel.Load.Valid WellStrength.bank plan := by
  intro a ha
  simp only [plan,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl <;> decide

theorem preserves (geometry : ℕ→ℕ) (v : ℕ→Parts) (i : ℕ)
    (hi : i ≠ 8 ∧ i ≠ 9 ∧ i ≠ 10 ∧ i ≠ 11) : values geometry v i=v i := by
  apply NaturalChannel.Load.values_preserves
  intro a ha
  simp only [plan,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl <;> tauto

theorem resets (geometry : ℕ→ℕ) (v : ℕ→Parts) :
    WellStrengthReset.canonical (values geometry v)=WellStrengthReset.canonical v := by
  apply resetList_congr
  intro i hi
  apply preserves
  simp only [WellStrengthReset.targets,List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
  omega

def coupling (geometry : ℕ→ℕ) (v : ℕ→Parts) : ℚ :=
  if geometry 976 ≠ geometry 979 then (v 5).value else
    if geometry 977 ≠ geometry 980 then (v 6).value else (v 7).value

theorem selected (geometry : ℕ→ℕ) (v : ℕ→Parts) (hv : WellStrengthReset.canonical v=v) :
    WellAxisMachine.selected (values geometry v)=coupling geometry v := by
  have zero (k : ℕ) (hk : k∈WellStrengthReset.targets) : v k=Parts.literal 0 := by
    rw [←hv,WellStrengthReset.canonical,resetList_values,ite_eq_left hk]
  have h8 := zero 8 (by decide)
  have h9 := zero 9 (by decide)
  have h10 := zero 10 (by decide)
  have h11 := zero 11 (by decide)
  simp [WellAxisMachine.selected,values,plan,NaturalChannel.Load.values,
    h8,h9,h10,h11,NaturalChannel.replace,Parts.value,Parts.literal,coupling]

theorem executes (geometry : ℕ→ℕ) (v : ℕ→Parts) (B : ℕ)
    (hw : WidthBank WellStrength.bank B v) (hg : Good WellStrength.bank v)
    (hn : ∀a∈plan,(geometry a.1).bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hr : Ready WellStrength.bank v s)
    (words : ∀a∈plan,Word s.val a.1 (geometry a.1)) :
    ∃cost t,Executes input tape code cost s t ∧ cost ≤ 4*(37*B+39)+1 ∧
      Ready WellStrength.bank (values geometry v) t ∧ WidthBank WellStrength.bank B (values geometry v) ∧
      Good WellStrength.bank (values geometry v) ∧ BinaryPrecision.Frame (ids WellStrength.bank) s.val t.val :=
  NaturalChannel.Load.executes WellStrength.bank plan valid geometry v B hw hg hn input tape s hr words

#print axioms selected
#print axioms executes
end Maxwell.Continuum.RationalDataflow.WellMediatorLoad
