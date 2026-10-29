import Maxwell.Cost.PhysicalDecoder.Entry
import Maxwell.Composition.SourcePhysicalDecoderRecords

/-! The runtime coefficient operands are exactly the calibrated decoder's
mode, strength, and original normalization scales. -/
namespace Maxwell.Cost.PhysicalDecoder.Binding
open Maxwell.Composition Maxwell.Logical

def data (q v beta lambda : ℚ) : Arithmetic.Data :=
  ![q.num.natAbs,q.den,v.num.toNat,v.den,beta.num.toNat,beta.den,lambda.num.toNat,lambda.den]

theorem signed_fraction (q : ℚ) :
    RationalCanonical.value (decide (q.num<0)) q.num.natAbs q.den=q := by
  have h : (if decide (q.num<0) then -(q.num.natAbs:ℚ) else q.num.natAbs)=(q.num:ℚ) := by
    generalize q.num=z
    cases z <;> simp
  unfold RationalCanonical.value
  rw [h,Rat.num_div_den]

theorem unsigned_fraction (q : ℚ) (h : 0 ≤ q) : (q.num.toNat:ℚ)/q.den=q := by
  rw [← Int.cast_natCast,Int.toNat_of_nonneg (Rat.num_nonneg.mpr h),Rat.num_div_den]

theorem data_valid (q v beta lambda : ℚ) (hl : 0 < lambda) :
    Arithmetic.Valid (data q v beta lambda) := by
  refine ⟨q.den_pos,v.den_pos,beta.den_pos,?_⟩
  change 0 < lambda.num.toNat
  have h := Rat.num_pos.mpr hl
  omega

theorem data_fraction (q v beta lambda : ℚ) (hv : 0 ≤ v) (hb : 0 ≤ beta) (hl : 0 ≤ lambda) :
    Arithmetic.fraction (data q v beta lambda) (decide (q.num<0))=(beta/lambda)*(v*q) := by
  change ((beta.num.toNat:ℚ)/beta.den)/((lambda.num.toNat:ℚ)/lambda.den)*
    ((v.num.toNat:ℚ)/v.den)*RationalCanonical.value (decide (q.num<0)) q.num.natAbs q.den = _
  rw [unsigned_fraction beta hb,unsigned_fraction lambda hl,unsigned_fraction v hv,signed_fraction]
  ring

/-- Stored common denominators need not be reduced. Only the represented
fractions enter the actual decoder coefficient. -/
theorem fraction_of_operands (x : Arithmetic.Data) (negative : Bool)
    (q v beta lambda : ℚ)
    (hq : RationalCanonical.value negative (x 0) (x 1) = q)
    (hv : (x 2 : ℚ)/(x 3) = v) (hb : (x 4 : ℚ)/(x 5) = beta)
    (hl : (x 6 : ℚ)/(x 7) = lambda) :
    Arithmetic.fraction x negative = (beta/lambda)*(v*q) := by
  unfold Arithmetic.fraction
  rw [hq, hv, hb, hl]
  ring

variable (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
variable (ζ : ℚ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hd : P.spacing.minimumDistance ≤ d)
variable (qhat : SourcePhysicalDecoder.Local P → ℚ)
variable (v : SourceDecoration.Vertex S precision → ℚ) (format : Target.FixedPointFormat)

theorem actual_weight (i : Fin S.n) (j : SourcePhysicalDecoder.Local P)
    (hv : 0 ≤ v (SourcePhysicalDecoder.vertex S precision i)) :
    Arithmetic.fraction (data (qhat j) (v (SourcePhysicalDecoder.vertex S precision i))
      (Normalization.sourceScale S) (Normalization.matrixScale S)) (decide ((qhat j).num<0)) =
    (SourcePhysicalDecoder.decoder P S precision d ζ hζ hζ1 hd qhat v format).weight i
      (finProdFinEquiv (i,j)) := by
  have hb : 0 ≤ Normalization.sourceScale S := Normalization.magnitudeMax_nonneg _
  have hl : 0 ≤ Normalization.matrixScale S :=
    mul_nonneg (Nat.cast_nonneg _) (Normalization.matrixMax_nonneg S)
  simp only [SourcePhysicalDecoder.decoder,SourcePhysicalDecoder.unscaled,
    selectScaleDecoder,localModeDecoder,id_eq,Equiv.symm_apply_apply]
  exact data_fraction _ _ _ _ hv hb hl

theorem actual_weight_of_operands (i : Fin S.n) (j : SourcePhysicalDecoder.Local P)
    (x : Arithmetic.Data) (negative : Bool)
    (hq : RationalCanonical.value negative (x 0) (x 1) = qhat j)
    (hv : (x 2 : ℚ)/(x 3) = v (SourcePhysicalDecoder.vertex S precision i))
    (hb : (x 4 : ℚ)/(x 5) = Normalization.sourceScale S)
    (hl : (x 6 : ℚ)/(x 7) = Normalization.matrixScale S) :
    Arithmetic.fraction x negative =
      (SourcePhysicalDecoder.decoder P S precision d ζ hζ hζ1 hd qhat v format).weight i
        (finProdFinEquiv (i,j)) := by
  simp only [SourcePhysicalDecoder.decoder, SourcePhysicalDecoder.unscaled,
    selectScaleDecoder, localModeDecoder, id_eq, Equiv.symm_apply_apply]
  exact fraction_of_operands x negative _ _ _ _ hq hv hb hl

end Maxwell.Cost.PhysicalDecoder.Binding
