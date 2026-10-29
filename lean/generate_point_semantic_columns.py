# /// script
# requires-python = ">=3.11"
# ///
"""Compose checked scalar data into actual point column and matrix facts."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
OUT=ROOT/'Maxwell/Certificate/PointInertia';modules=[]
for label,shift in [('Lower',1),('Upper',5)]:
 for col in range(28):
  name=f'{label}Semantic{col:02d}'
  s=f'''import Maxwell.Certificate.PointActionWitness.{label}C{col:02d}Complete
import Maxwell.Certificate.LowCompressionWitness.{label}LiteralBinding{col:02d}
import Maxwell.Certificate.FieldNormWitness.{label}Field{col:02d}
import Maxwell.Certificate.FieldNormWitness.{label}Applied{col:02d}
import Maxwell.Certificate.FieldNormWitness.{label}FieldBounds
import Maxwell.Certificate.FieldNormWitness.{label}AppliedBounds
namespace Maxwell.Certificate.PointInertia
open FourierBinding ProjectionWitness PointActionWitness LowCompressionWitness FieldNormWitness AppliedWitness
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem {label}LowActualField_col{col} (k : Fin 42) :
    ({label}LowField k {col}).Contains 52 ((projectedField {label}Raw{col}) ({label}LowIndex k)) := by
  rw [{label}LowField_col{col}]
  exact {label}Result{col}_contains _ _
theorem {label}LowActualApplied_col{col} (k : Fin 42) :
    ({label}LowApplied k {col}).Contains 52
      (((pointBaseMagneticMatrix ({shift}/256)).toEuclideanLin (projectedField {label}Raw{col})) ({label}LowIndex k)) := by
  rw [{label}LowApplied_col{col}]
  exact {label}C{col:02d}_actual_action_contains _ _
theorem {label}ActualField_high{col} :
    ‖frequencyRestriction lowFrequenciesᶜ (projectedField {label}Raw{col})‖^2 ≤
      ({label}FieldBounds {col} : ℝ)/(2:ℝ)^104 :=
  high_norm_sq_bound {label}Result{col} (projectedField {label}Raw{col}) _
    (fun f j => {label}Result{col}_contains f j) {label}Field{col:02d}_bound
theorem {label}ActualApplied_high{col} :
    ‖frequencyRestriction lowFrequenciesᶜ
      ((pointBaseMagneticMatrix ({shift}/256)).toEuclideanLin (projectedField {label}Raw{col}))‖^2 ≤
      ({label}AppliedBounds {col} : ℝ)/(2:ℝ)^104 :=
  high_norm_sq_bound {label}Applied{col} _ _
    (fun f j => {label}C{col:02d}_actual_action_contains f j) {label}Applied{col:02d}_bound
end Maxwell.Certificate.PointInertia
'''
  (OUT/f'{name}.lean').write_text(s);modules.append(f'Maxwell.Certificate.PointInertia.{name}')
 s=''.join(f'import Maxwell.Certificate.PointInertia.{label}Semantic{col:02d}\n' for col in range(28))
 s+=f'import Maxwell.Certificate.PointInertia.TrialNorms\nimport Maxwell.Certificate.LowCompressionWitness.{label}Checked\nimport Maxwell.Certificate.LowCompressionWitness.{label}Index\n'
 s+=f'''noncomputable section
namespace Maxwell.Certificate.PointInertia
open FourierBinding ProjectionWitness LowCompressionWitness FieldNormWitness
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def {label}RawColumns : Fin 28 → (Frequency → Fin 3 → DyadicRectangle) := !['''+', '.join(f'{label}Raw{j}' for j in range(28))+f''']
def {label}TrialColumns (i : Fin 28) : PointTransverseSpace := transverseField ({label}RawColumns i)
def {label}LowTrial := lowTrialMatrix {label}LowIndex {label}TrialColumns
def {label}LowAction := lowActionMatrix {label}LowIndex (pointBaseMagneticMatrix ({shift}/256)) {label}TrialColumns
'''
 for kind,actual,expr in [('Field','Field',f'{label}LowTrial'),('Applied','Applied',f'{label}LowAction')]:
  s+=f'theorem {label}Low{kind}_contains (k i) : ({label}Low{kind} k i).Contains 52 ({expr} k i) := by\n  fin_cases i\n'
  for j in range(28):s+=f'  · exact {label}LowActual{actual}_col{j} k\n'
 s+=f'''theorem {label}Compression_contains (i j) : ({label}Compression i j).Contains 52
    (HermitianCompression.matrix {label}LowTrial {label}LowAction i j) :=
  HermitianCompression.contains _ _ {label}LowField {label}LowApplied {label}Compression
    {label}LowField_contains {label}LowApplied_contains {label}DotCheck_all i j
'''
 for kind,body in [('Field',f'({label}TrialColumns i : FourierSpace)'),('Applied',f'((pointBaseMagneticMatrix ({shift}/256)).toEuclideanLin ({label}TrialColumns i : FourierSpace))')]:
  s+=f'''theorem {label}{kind}_high_column (i : Fin 28) :
    ‖frequencyRestriction lowFrequenciesᶜ {body}‖^2 ≤
      ({label}{kind}Bounds i : ℝ)/(2:ℝ)^104 := by
  fin_cases i
'''
  for j in range(28):s+=f'  · exact {label}Actual{kind}_high{j}\n'
 s+=f'''theorem {label}Field_high_squares :
    ∑ i, ‖frequencyRestriction lowFrequenciesᶜ ({label}TrialColumns i : FourierSpace)‖^2 ≤ (16:ℝ)^2 := by
  have h := column_squares_le_of_dyadic _ {label}FieldBounds _ {label}Field_high_column {label}FieldBounds_sum
  norm_num at h ⊢
  exact h
theorem {label}Applied_high_squares :
    ∑ i, ‖frequencyRestriction lowFrequenciesᶜ
      ((pointBaseMagneticMatrix ({shift}/256)).toEuclideanLin ({label}TrialColumns i : FourierSpace))‖^2 ≤ (1/(2:ℝ)^23)^2 := by
  have h := column_squares_le_of_dyadic _ {label}AppliedBounds _ {label}Applied_high_column {label}AppliedBounds_sum
  norm_num at h ⊢
  exact h
'''
 s+='end Maxwell.Certificate.PointInertia\n'
 (OUT/f'{label}Columns.lean').write_text(s);modules.append(f'Maxwell.Certificate.PointInertia.{label}Columns')
(ROOT/'evidence/point_inertia_proposals/semantic_column_modules.json').write_text(json.dumps(modules,indent=2)+'\n')
for label,shift,n in [('Lower',1,2),('Upper',5,4)]:
 s=f'''import Maxwell.Certificate.PointInertia.{label}Columns
import Maxwell.Certificate.PointInertia.FiniteFinish
import Maxwell.Certificate.LowCompressionWitness.{label}NegativeSigned
import Maxwell.Certificate.LowCompressionWitness.{label}PositiveSigned
namespace Maxwell.Certificate.PointInertia
open LowCompressionWitness
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem {label}Transverse_inertia :
    (Finset.univ.filter fun i => (pointBaseTransverse_symmetric ({shift}/256)).eigenvalues rfl i < 0).card = {n} ∧
    (Finset.univ.filter fun i => (pointBaseTransverse_symmetric ({shift}/256)).eigenvalues rfl i = 0).card = 0 ∧
    (Finset.univ.filter fun i => 0 < (pointBaseTransverse_symmetric ({shift}/256)).eigenvalues rfl i).card = {4000-n} := by
  apply point_inertia_of_finite_checks ({shift}/256) (by norm_num) (by norm_num) {n} (by omega)
    {label}LowIndex {label}LowIndex_mem {label}LowIndex_injective {label}TrialColumns
    {label}NegativeSelect {label}PositiveSelect
  · intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [{label}NegativeSelect] at hv
    omega
  · intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [{label}PositiveSelect] at hv
    omega
  · exact {label}Negative_selected_psd _ _ {label}Compression_contains
  · exact {label}Positive_selected_psd _ _ {label}Compression_contains
  · exact {label}Field_high_squares
  · simpa only [zpow_neg, zpow_ofNat, one_div] using {label}Applied_high_squares
end Maxwell.Certificate.PointInertia
'''
 (OUT/f'{label}Verified.lean').write_text(s);modules.append(f'Maxwell.Certificate.PointInertia.{label}Verified')
s='''import Maxwell.Certificate.PointInertia.LowerVerified
import Maxwell.Certificate.PointInertia.UpperVerified
import Maxwell.Certificate.PointInertia.ThresholdBridge
namespace Maxwell.Certificate.PointInertia
 theorem pointBaseInertia_verified : PointWitness.PointBaseInertia :=
   pointBaseInertia_of_transverse_counts LowerTransverse_inertia.1 UpperTransverse_inertia.1
 theorem pointClusterComplementGap_verified : PointWitness.PointClusterComplementGap :=
   PointWitness.pointClusterComplementGap_of_base_inertia pointBaseInertia_verified
end Maxwell.Certificate.PointInertia
'''
(OUT/'Verified.lean').write_text(s);modules.append('Maxwell.Certificate.PointInertia.Verified')
(ROOT/'evidence/point_inertia_proposals/semantic_column_modules.json').write_text(json.dumps(modules,indent=2)+'\n')
