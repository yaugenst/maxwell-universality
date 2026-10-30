import Maxwell.Continuum.H1Curl

/-! The cutoff curl-curl commutator is an explicit L² expression in
the field and its first weak derivatives. No second derivatives of the
auxiliary field are assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.SchwartzMultiplier

open MeasureTheory FourierSobolev
open scoped SchwartzMap

def secondProductRemainder (θ : SchwartzMap Space ℂ) {f : FieldL2}
    (Df : H1Data f) (a b c : Fin 3) : ScalarL2 :=
  scalar (partialSchwartz a (partialSchwartz b θ)) (f c)+
    scalar (partialSchwartz b θ) (Df.derivative a c)+
    scalar (partialSchwartz a θ) (Df.derivative b c)

theorem second_partial_product (θ : SchwartzMap Space ℂ) {f : FieldL2}
    (Df : H1Data f) (a b c : Fin 3) :
    partialDistribution a (partialDistribution b (Lp.toTemperedDistribution (scalar θ (f c)))) =
      TemperedDistribution.smulLeftCLM ℂ θ
        (partialDistribution a (partialDistribution b (Lp.toTemperedDistribution (f c))))+
      Lp.toTemperedDistribution (secondProductRemainder θ Df a b c) := by
  simp only [scalar_distribution, partialDistribution_product, map_add,
    secondProductRemainder, scalar_distribution_add, Df.weak_derivative]
  abel

def curlCurlCommutator (θ : SchwartzMap Space ℂ) {f : FieldL2} (Df : H1Data f) : FieldL2 :=
  WithLp.toLp 2 (fun i =>
    secondProductRemainder θ Df (i+1) ((i+2)+1) ((i+2)+2)-
      secondProductRemainder θ Df (i+1) ((i+2)+2) ((i+2)+1)-
      (secondProductRemainder θ Df (i+2) ((i+1)+1) ((i+1)+2)-
        secondProductRemainder θ Df (i+2) ((i+1)+2) ((i+1)+1)))

theorem scalar_distribution_sub (u v : ScalarL2) :
    Lp.toTemperedDistribution (u-v) = Lp.toTemperedDistribution u-Lp.toTemperedDistribution v :=
  map_sub (Lp.toTemperedDistributionCLM ℂ (volume : Measure Space) 2) u v

theorem curlCurl_product_distribution (θ : SchwartzMap Space ℂ) {f : FieldL2}
    (Df : H1Data f) (i : Fin 3) :
    curlDistribution (curlDistribution (fieldDistribution (field θ f))) i =
      TemperedDistribution.smulLeftCLM ℂ θ
        (curlDistribution (curlDistribution (fieldDistribution f)) i)+
      Lp.toTemperedDistribution (curlCurlCommutator θ Df i) := by
  simp only [curlDistribution_apply, fieldDistribution_apply, field_apply,
    map_sub, second_partial_product θ Df, curlCurlCommutator, WithLp.ofLp_toLp, scalar_distribution_sub]
  abel

theorem curlCurl_product_L2 (θ : SchwartzMap Space ℂ) {f A : FieldL2}
    (Df : H1Data f) (hA : curlDistribution (curlDistribution (fieldDistribution f)) = fieldDistribution A) :
    curlDistribution (curlDistribution (fieldDistribution (field θ f))) =
      fieldDistribution (field θ A+curlCurlCommutator θ Df) := by
  funext i
  rw [curlCurl_product_distribution θ Df, hA]
  simp only [fieldDistribution_apply, PiLp.add_apply, field_apply, scalar_distribution_add, scalar_distribution]

#print axioms curlCurl_product_L2

end Maxwell.Continuum.SchwartzMultiplier
