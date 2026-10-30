import Maxwell.Continuum.SchwartzProductDerivative

/-! The actual L² curl supplied by first weak derivatives. -/

noncomputable section

namespace Maxwell.Continuum.FourierSobolev

open MeasureTheory

def H1Data.curl {f : FieldL2} (Df : H1Data f) : FieldL2 :=
  WithLp.toLp 2 (fun i => Df.derivative (i+1) (i+2)-Df.derivative (i+2) (i+1))

theorem H1Data.curl_distribution {f : FieldL2} (Df : H1Data f) :
    curlDistribution (fieldDistribution f) = fieldDistribution Df.curl := by
  funext i
  simp only [curlDistribution_apply, fieldDistribution_apply, Df.weak_derivative,
    H1Data.curl]
  exact (map_sub (Lp.toTemperedDistributionCLM ℂ (volume : Measure Space) 2) _ _).symm

def H1Data.curlGraph {f : FieldL2} (Df : H1Data f) : CurlGraphAmbient :=
  WithLp.toLp 2 (f, Df.curl)

theorem H1Data.curlGraph_mem {f : FieldL2} (Df : H1Data f) : Df.curlGraph ∈ weakCurlGraph :=
  (mem_weakCurlGraph _).mpr Df.curl_distribution

#print axioms H1Data.curl_distribution

end Maxwell.Continuum.FourierSobolev
