import Maxwell.Continuum.StoredWellStream

/-! A linear record-count bound for the actual charged well serializer.
The retained common payload is copied at every well and counted in full. -/
namespace Maxwell.Continuum.WellOutput
set_option maxHeartbeats 5000000

def workSize (BG B : ℕ) (profile template : List Bool) : ℕ :=
  (BG+B+5)^2+profile.length+template.length+1

theorem workSize_bounds (BG B : ℕ) (profile template : List Bool) :
    (BG+3)^2≤workSize BG B profile template ∧ (B+5)^2≤workSize BG B profile template ∧
      BG+1≤workSize BG B profile template ∧ profile.length+template.length≤workSize BG B profile template ∧
      1≤workSize BG B profile template := by
  unfold workSize
  constructor
  · have := Nat.pow_le_pow_left (by omega : BG+3≤BG+B+5) 2
    omega
  constructor
  · have := Nat.pow_le_pow_left (by omega : B+5≤BG+B+5) 2
    omega
  constructor
  · nlinarith only [Nat.zero_le BG,Nat.zero_le B]
  constructor <;> omega

theorem stepCost_bound (BG B : ℕ) (profile template : List Bool) :
    stepCost BG B profile template≤2^32*workSize BG B profile template := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := workSize_bounds BG B profile template
  unfold stepCost
  nlinarith only [h0,h1,h3,h4]

theorem pathCost_bound (BG B count : ℕ) (profile template : List Bool) :
    pathCost BG B count profile template≤2^33*(count+1)*workSize BG B profile template := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := workSize_bounds BG B profile template
  have hs := stepCost_bound BG B profile template
  have ha : 13*BG+15≤32*workSize BG B profile template := by omega
  have hfirst := Nat.mul_le_mul_left (2^27) h0
  have hcounter := Nat.mul_le_mul_left (count+1) ha
  have hstep := Nat.mul_le_mul_left count hs
  unfold pathCost
  nlinarith only [hfirst,hcounter,hstep,h4,Nat.zero_le count]

theorem originalCost_bound (BG B vertices : ℕ) (profile template : List Bool) :
    originalCost BG B vertices profile template≤2^33*(vertices+1)*workSize BG B profile template := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := workSize_bounds BG B profile template
  have hs := stepCost_bound BG B profile template
  have ha : 13*BG+15≤32*workSize BG B profile template := by omega
  have hl : 21*BG+21≤32*workSize BG B profile template := by omega
  have hfirst := Nat.mul_le_mul_left (2^23) h0
  have hcounter := Nat.mul_le_mul_left (vertices+1) ha
  have hstep := Nat.mul_le_mul_left vertices hs
  unfold originalCost
  nlinarith only [hfirst,hcounter,hstep,hl,h4,Nat.zero_le vertices]

theorem loadedPathsCost_bound (BG B edges bound : ℕ) (profile template : List Bool) :
    loadedPathsCost BG B edges bound profile template≤
      2^35*(edges*(bound+1)+1)*workSize BG B profile template := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := workSize_bounds BG B profile template
  have hs := pathCost_bound BG B bound profile template
  have ha : 13*BG+15≤32*workSize BG B profile template := by omega
  have hl : 21*BG+21≤32*workSize BG B profile template := by omega
  have hfirst := Nat.mul_le_mul_left (2^23) h0
  have hcounter := Nat.mul_le_mul_left (edges+1) ha
  have hstep := Nat.mul_le_mul_left edges hs
  unfold loadedPathsCost
  nlinarith only [hfirst,hcounter,hstep,hl,h4,Nat.zero_le edges,Nat.zero_le bound,
    Nat.zero_le (edges*bound*workSize BG B profile template)]

theorem costBound_polynomial (BG B vertices edges bound : ℕ) (profile template : List Bool) :
    costBound BG B vertices edges bound profile template≤
      2^40*(vertices+edges*(bound+1)+1)*workSize BG B profile template := by
  have ho := originalCost_bound BG B vertices profile template
  have hp := loadedPathsCost_bound BG B edges bound profile template
  obtain ⟨h0,h1,h2,h3,h4⟩ := workSize_bounds BG B profile template
  have hh : 20*BG+24≤64*workSize BG B profile template := by omega
  unfold costBound
  nlinarith only [ho,hp,hh,h4,Nat.zero_le vertices,Nat.zero_le edges,Nat.zero_le bound,
    Nat.zero_le (vertices*workSize BG B profile template),
    Nat.zero_le (edges*(bound+1)*workSize BG B profile template)]

#print axioms costBound_polynomial
end Maxwell.Continuum.WellOutput
