import Maxwell.Composition.SourceSeedStream
import Maxwell.Cost.PhysicalSource.SeedArithmetic
import Maxwell.Cost.NormalizeRatio.SourceData

/-! Bind the source writer's actual integer arithmetic to the exact selected
physical seed, with the original RHS and its retained normalization pair. -/
noncomputable section
namespace Maxwell.Composition.SourceSeedWords
open Maxwell.Defect Maxwell.Logical
open Maxwell.Composition.PhysicalSource
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000

def positive (q : ℚ) : ℕ := if q.num<0 then 0 else q.num.natAbs
def negative (q : ℚ) : ℕ := if q.num<0 then q.num.natAbs else 0

theorem signed_value (q : ℚ) : (positive q:ℚ)-negative q=q.num := by
  have h := Cost.NormalizeRatio.signed_natAbs q
  by_cases hn : q.num<0
  · simpa [positive,negative,hn] using h
  · simpa [positive,negative,hn] using h

def incidentCount (P : PhysicalPlatform) (k : Local P) : ℕ :=
  (ScalarDefect.hits P.defect (ScalarDefect.edgeEmbedding P.defect k)).card

theorem weight_eq (P : PhysicalPlatform) (k : Local P) :
    ScalarDefect.coordinateWeight P.defect k = (incidentCount P k:ℚ)/4 :=
  ScalarDefect.weight_eq_count _ _

theorem incidentCount_pos (P : PhysicalPlatform) (k : Local P) : 0 < incidentCount P k := by
  have h := (ScalarDefect.coordinateWeight_bounds P.defect k).1
  rw [weight_eq] at h
  have h' : (0:ℚ) < incidentCount P k := by linarith
  exact_mod_cast h'

def inputs (P : PhysicalPlatform) (S : Source.SparseSystem) (q : Local P→ℚ)
    (i : Fin S.n) (k : Local P) : ℕ→ℕ
  | 360 => (S.source i).num.natAbs
  | 361 => (S.source i).den
  | 362 => positive (q k)
  | 363 => negative (q k)
  | 364 => (q k).den
  | 365 => incidentCount P k
  | 366 => positive (S.source i)
  | 367 => negative (S.source i)
  | 506 => (Cost.NormalizeRatio.sourceScalePair S).1
  | 507 => (Cost.NormalizeRatio.sourceScalePair S).2
  | _ => 0

theorem value_eq (P : PhysicalPlatform) (S : Source.SparseSystem) (q : Local P→ℚ)
    (i : Fin S.n) (k : Local P) :
    Cost.PhysicalSource.SeedArithmetic.value (inputs P S q i k) =
      SourceSeedStream.value P S q (i,k) := by
  simp only [Cost.PhysicalSource.SeedArithmetic.value,inputs,signed_value]
  rw [(q k).num_div_den,(S.source i).num_div_den,Cost.NormalizeRatio.sourceScalePair_value]
  simp only [SourceSeedStream.value,Normalization.normalizedSource,weight_eq,inv_div]
  ring

theorem fraction_eq (P : PhysicalPlatform) (S : Source.SparseSystem) (q : Local P→ℚ)
    (i : Fin S.n) (k : Local P) :
    ((Cost.PhysicalSource.SeedArithmetic.positive (inputs P S q i k):ℚ)-
      Cost.PhysicalSource.SeedArithmetic.negative (inputs P S q i k)) /
        Cost.PhysicalSource.SeedArithmetic.denominator (inputs P S q i k) =
      SourceSeedStream.value P S q (i,k) := by
  rw [Cost.PhysicalSource.SeedArithmetic.fraction_value,value_eq]

theorem denominator_pos (P : PhysicalPlatform) (S : Source.SparseSystem) (q : Local P→ℚ)
    (hb : S.source≠0) (i : Fin S.n) (k : Local P) :
    0<Cost.PhysicalSource.SeedArithmetic.denominator (inputs P S q i k) := by
  apply Cost.PhysicalSource.SeedArithmetic.denominator_pos
  exact ⟨(S.source i).den_pos,(q k).den_pos,incidentCount_pos P k,
    (Cost.NormalizeRatio.sourceScalePair_positive S hb).1⟩

end Maxwell.Composition.SourceSeedWords
