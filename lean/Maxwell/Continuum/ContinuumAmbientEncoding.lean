import Maxwell.Continuum.ContinuumGeometryWords

/-! Explicit enumeration and Boolean representation of every ambient unit
cube, including all empty routing space and the boundary buffer. The separate
ball records retain their exact quadratic support inequalities. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.AmbientEncoding

def cubeBits {a b c : ℕ} (x : Fin a × Fin b × Fin c) : List Bool :=
  Codec.nat x.1.val++Codec.nat x.2.1.val++Codec.nat x.2.2.val

def bits (a b c : ℕ) : List Bool := Codec.list cubeBits (Codec.triples a b c)

theorem cubes_length (a b c : ℕ) : (Codec.triples a b c).length=a*b*c := by
  simp [Codec.triples,List.length_flatMap,Nat.mul_assoc]

theorem cubes_complete (a b c : ℕ) (x : Fin a × Fin b × Fin c) :
    x∈Codec.triples a b c := by
  rcases x with ⟨i,j,k⟩
  simp [Codec.triples]

theorem cubeBits_bound {a b c B : ℕ} (ha : a≤2^B) (hb : b≤2^B) (hc : c≤2^B)
    (x : Fin a × Fin b × Fin c) : (cubeBits x).length≤6*B+9 := by
  have hx := Codec.unsignedBitLength_mono (x.1.isLt.le.trans ha)
  have hy := Codec.unsignedBitLength_mono (x.2.1.isLt.le.trans hb)
  have hz := Codec.unsignedBitLength_mono (x.2.2.isLt.le.trans hc)
  rw [Dyadic.denominator_bitLength] at hx hy hz
  simp only [cubeBits,List.length_append,Codec.nat_length]
  omega

theorem bits_bound {a b c B : ℕ} (ha : a≤2^B) (hb : b≤2^B) (hc : c≤2^B) :
    (bits a b c).length≤(a*b*c+1)*(6*B+9) := by
  have hp : a*b*c≤2^(3*B) := by
    calc
      _≤2^B*2^B*2^B := Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc
      _=_ := by rw [← pow_add,← pow_add]; congr 1; omega
  have hs := Codec.unsignedBitLength_mono hp
  rw [Dyadic.denominator_bitLength] at hs
  have hl := Codec.list_length_le cubeBits (Codec.triples a b c) (6*B+9)
    (fun x _ => cubeBits_bound ha hb hc x)
  rw [cubes_length] at hl
  change (Codec.list cubeBits (Codec.triples a b c)).length≤_
  nlinarith only [hl,hs]

end Maxwell.Continuum.AmbientEncoding

namespace Maxwell.Continuum.RealizationParameters

attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude MasterConstants.exponent

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

def ambientCells := Codec.triples (Parameters.sourcePhysicalLengths p S hm 0)
  (Parameters.sourcePhysicalLengths p S hm 1) (Parameters.sourcePhysicalLengths p S hm 2)

def ambientBits : List Bool := AmbientEncoding.bits (Parameters.sourcePhysicalLengths p S hm 0)
  (Parameters.sourcePhysicalLengths p S hm 1) (Parameters.sourcePhysicalLengths p S hm 2)

theorem ambientCells_volume : ((ambientCells p S hm).length : ℝ)=
    (MeasureTheory.volume (BoxModes.openBox (BoxCutoff.side (box p S hm)))).toReal := by
  rw [BoxModes.openBox_volume_toReal _ (fun j => by unfold BoxCutoff.side; positivity),box_sides]
  simp only [ambientCells,AmbientEncoding.cubes_length,Fin.prod_univ_three,Nat.cast_mul]

theorem ambientBits_length (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    (ambientBits p S hm).length≤((ambientCells p S hm).length+1)*
      (6*analysisBits p+9)*logSize S := by
  have hs (k : Fin 3) := (physical_side_le_count p S hm k).trans (count_binary p S hm hm2 hu)
  have hh := AmbientEncoding.bits_bound (hs 0) (hs 1) (hs 2)
  change (ambientBits p S hm).length≤_ at hh
  have hℓ := Parameters.inputLog_pos S.nnz
  have hlin : 6*scaleBits p S+9≤(6*analysisBits p+9)*logSize S := by
    unfold scaleBits
    nlinarith only [hℓ]
  rw [← AmbientEncoding.cubes_length] at hh
  exact hh.trans (by
    change ((ambientCells p S hm).length+1)*(6*scaleBits p S+9)≤_
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left ((ambientCells p S hm).length+1) hlin)

def ambientBitCoefficient (p : Source.Parameters) : ℝ :=
  (Parameters.sourceVolumeCoefficient p+1)*(6*analysisBits p+9)

theorem ambientBits_polynomial (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    ((ambientBits p S hm).length : ℝ)≤ambientBitCoefficient p*
      (S.nnz : ℝ)^(3/2 : ℝ)*(logSize S : ℝ)^25 := by
  have hv := Parameters.source_physical_volume_bound p S hm hm2 hu
  rw [← ambientCells_volume p S hm] at hv
  have hℓ : (1 : ℝ)≤logSize S := by exact_mod_cast Parameters.inputLog_pos S.nnz
  have hm1 : (1 : ℝ)≤S.nnz := by exact_mod_cast hm
  have hmp : (1 : ℝ)≤(S.nnz : ℝ)^(3/2 : ℝ) := Real.one_le_rpow hm1 (by norm_num)
  have hlp : (1 : ℝ)≤(logSize S : ℝ)^24 := one_le_pow₀ hℓ
  have hbig : (1 : ℝ)≤(S.nnz : ℝ)^(3/2 : ℝ)*(logSize S : ℝ)^24 :=
    one_le_mul_of_one_le_of_one_le hmp hlp
  have hplus : ((ambientCells p S hm).length : ℝ)+1≤
      (Parameters.sourceVolumeCoefficient p+1)*(S.nnz : ℝ)^(3/2 : ℝ)*(logSize S : ℝ)^24 := by
    nlinarith only [hv,hbig]
  have hb : ((ambientBits p S hm).length : ℝ)≤
      (((ambientCells p S hm).length : ℝ)+1)*(6*(analysisBits p : ℝ)+9)*(logSize S : ℝ) := by
    exact_mod_cast ambientBits_length p S hm hm2 hu
  calc
    _≤((Parameters.sourceVolumeCoefficient p+1)*(S.nnz : ℝ)^(3/2 : ℝ)*(logSize S : ℝ)^24)*
        (6*(analysisBits p : ℝ)+9)*(logSize S : ℝ) := hb.trans (by gcongr)
    _=_ := by unfold ambientBitCoefficient; ring

#print axioms ambientCells_volume
#print axioms ambientBits_polynomial

end Maxwell.Continuum.RealizationParameters
