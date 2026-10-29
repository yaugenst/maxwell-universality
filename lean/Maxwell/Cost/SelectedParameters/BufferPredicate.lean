import Maxwell.Cost.SelectedParameters.BufferValues

namespace Maxwell.Cost.SelectedParameters.Buffer
set_option maxHeartbeats 1500000

/-- Clearing the three positive stored denominators gives exactly the
natural-number comparison performed by the finite machine. -/
theorem test_iff_fraction (d : Data) (n : ℕ) (hb : 0 < d.b) (hv : 0 < d.v) (hf : 0 < d.f) :
    Test d n ↔ ((d.u:ℚ)/d.v)*((d.m:ℚ)+(d.e:ℚ)/d.f*((d.s:ℚ)+n+1)^3)^2*
      ((d.a:ℚ)/d.b)^n ≤ 1 := by
  have hbq : (d.b:ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hvq : (d.v:ℚ) ≠ 0 := by exact_mod_cast hv.ne'
  have hfq : (d.f:ℚ) ≠ 0 := by exact_mod_cast hf.ne'
  have hright : (0:ℚ) < right d n := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos hv (pow_pos hf 2)) (pow_pos hb n)
  have heq : ((d.u:ℚ)/d.v)*((d.m:ℚ)+(d.e:ℚ)/d.f*((d.s:ℚ)+n+1)^3)^2*
      ((d.a:ℚ)/d.b)^n = (left d n:ℚ)/(right d n) := by
    simp only [left,right,polynomial,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one,div_pow]
    field_simp
  rw [heq,div_le_one hright]
  exact_mod_cast (Iff.rfl : Test d n ↔ left d n ≤ right d n)

/-- The supplied fraction is the actual selected coefficient 128J/(gτζ²).
No real logarithm is evaluated by the executable comparison. -/
theorem test_iff_rationalTest (d : Data) (J g τ ζ : ℚ) (n : ℕ)
    (hb : 0 < d.b) (hv : 0 < d.v) (hf : 0 < d.f)
    (hg : 0 < g) (hτ : 0 < τ) (hζ : 0 < ζ)
    (huv : (d.u:ℚ)/d.v = 128*J/(g*τ*ζ^2)) :
    Test d n ↔ Realization.Buffer.rationalTest ((d.a:ℚ)/d.b) J g ((d.e:ℚ)/d.f) τ ζ d.m d.s n := by
  rw [test_iff_fraction d n hb hv hf,huv]
  have heq : (128*J/(g*τ*ζ^2))*((d.m:ℚ)+(d.e:ℚ)/d.f*((d.s:ℚ)+n+1)^3)^2*
      ((d.a:ℚ)/d.b)^n =
      ((4*J/g)*(16*((d.m:ℚ)+(d.e:ℚ)/d.f*((d.s:ℚ)+n+1)^3)^2/τ)*((d.a:ℚ)/d.b)^n)/(ζ^2/2) := by
    field_simp
    ring
  rw [heq,div_le_one (by positivity : (0:ℚ) < ζ^2/2)]
  rfl

end Maxwell.Cost.SelectedParameters.Buffer
