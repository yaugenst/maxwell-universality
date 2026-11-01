import Maxwell.Continuum.ContinuumDescriptionSchema
import Maxwell.Cost.DecoderParser.Width

/-! The complete physical parser has only a polylogarithmic overhead per
emitted bit. Outer record counts are bounded separately from local records. -/

noncomputable section
namespace Maxwell.Continuum.DescriptionSchema
open Maxwell.Cost.DecoderParser RealizationParameters
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent computedEnclosures

def widthCoefficient (p : Source.Parameters) : ℕ :=
  headerBitCoefficient p+recordBitCoefficient p+inputBits p+8*analysisBits p+30

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

theorem data_width (hm2 : 2≤S.nnz) (hp : Source.Promises p S) (hb : S.source≠0)
    (j : Fin (drawCount p S hm)) :
    WidthBound shape (data p S hm j) (widthCoefficient p*(logSize S)^25) := by
  let B := widthCoefficient p*(logSize S)^25
  have hℓ : 0<logSize S := Parameters.inputLog_pos S.nnz
  have hl : logSize S≤(logSize S)^25 := le_self_pow₀ (by omega) (by decide : (25:ℕ)≠0)
  have lift (c : ℕ) (hc : c≤widthCoefficient p) : c*logSize S≤B :=
    (Nat.mul_le_mul_left c hl).trans (Nat.mul_le_mul_right _ hc)
  have hheader : WidthBound headerShape (headerData p S hm j) B := by
    apply widthBound_of_length
    rw [header_wire]
    exact (headerBits_length p S hm hm2 hp j).trans (lift _ (by unfold widthCoefficient;omega))
  have hside (k : Fin 3) : Parameters.sourcePhysicalLengths p S hm k≤2^scaleBits p S :=
    (physical_side_le_count p S hm k).trans (count_binary p S hm hm2 hp.1)
  have hambient : (ambientCells p S hm).length≤2^(3*scaleBits p S) := by
    rw [ambientCells,AmbientEncoding.cubes_length]
    calc
      _≤2^scaleBits p S*2^scaleBits p S*2^scaleBits p S :=
        Nat.mul_le_mul (Nat.mul_le_mul (hside 0) (hside 1)) (hside 2)
      _=_ := by rw [← pow_add,← pow_add];congr 1;omega
  have hcountAmbient : (ambientCells p S hm).length.bits.length≤B := by
    have h := Codec.unsignedBitLength_mono hambient
    rw [Dyadic.denominator_bitLength] at h
    simp only [Codec.unsignedBitLength_eq_size,← Nat.size_eq_bits_len] at h
    exact h.trans ((by unfold scaleBits;nlinarith only [hℓ] :
      3*scaleBits p S+1≤(3*analysisBits p+1)*logSize S).trans
        (lift _ (by unfold widthCoefficient;omega)))
  have hcube (x : Fin (Parameters.sourcePhysicalLengths p S hm 0) ×
      Fin (Parameters.sourcePhysicalLengths p S hm 1) ×
      Fin (Parameters.sourcePhysicalLengths p S hm 2)) : WidthBound cubeShape (cubeData x) B := by
    apply widthBound_of_length
    rw [cube_wire]
    exact (AmbientEncoding.cubeBits_bound (hside 0) (hside 1) (hside 2) x).trans
      ((by unfold scaleBits;nlinarith only [hℓ] :
        6*scaleBits p S+9≤(6*analysisBits p+9)*logSize S).trans
          (lift _ (by unfold widthCoefficient;omega)))
  have hsites : sites p S hm≤2^(inputBits p*logSize S) := by
    exact_mod_cast (input_binary p S hm hm2 hp.1).2.1
  have hcountSites : (sites p S hm).bits.length≤B := by
    have h := Codec.unsignedBitLength_mono hsites
    rw [Dyadic.denominator_bitLength] at h
    simp only [Codec.unsignedBitLength_eq_size,← Nat.size_eq_bits_len] at h
    exact h.trans ((by nlinarith only [hℓ] : inputBits p*logSize S+1≤(inputBits p+1)*logSize S).trans
      (lift _ (by unfold widthCoefficient;omega)))
  have hcountSource : S.n.bits.length≤B := by
    have h := (Codec.unsignedBitLength_mono (Source.dimension_le_nnz S hp.1)).trans
      (Codec.unsignedBitLength_mono (Parameters.input_le_binary S.nnz))
    rw [Dyadic.denominator_bitLength] at h
    simp only [Codec.unsignedBitLength_eq_size,← Nat.size_eq_bits_len] at h
    exact h.trans ((by change logSize S+1≤2*logSize S;omega :
        Parameters.inputLog S.nnz+1≤2*logSize S).trans
      (lift 2 (by unfold widthCoefficient;omega)))
  have hrecord : recordBitCoefficient p*(logSize S)^25≤B :=
    Nat.mul_le_mul_right _ (by unfold widthCoefficient;omega)
  have hwell (i) : WidthBound wellShape (wellData p S hm i) B := by
    apply widthBound_of_length
    rw [well_wire]
    exact (wellBits_length p S hm hm2 hp.1 hb i).trans hrecord
  have hsource (i) : WidthBound sourceShape (sourceData p S hm i) B := by
    apply widthBound_of_length
    rw [source_wire]
    exact (sourceRecordBits_length p S hm hm2 hp.1 hb i).trans hrecord
  have hplacement (i) : WidthBound placementShape (placementData p S hm i) B := by
    apply widthBound_of_length
    rw [placement_wire]
    exact (placementBits_length p S hm hm2 hp.1 i).trans
      (lift _ (by unfold widthCoefficient;omega))
  change WidthBound shape (data p S hm j) B
  refine ⟨hheader,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · simpa using hcountAmbient
  · intro x hx
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
    exact hcube y
  · simpa [Maxwell.Composition.SourceDecorationEnumeration.vertexList_length,sites] using hcountSites
  · intro x hx
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
    exact hwell y
  · simpa using hcountSource
  · intro x hx
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
    exact hsource y
  · simpa using hcountSource
  · intro x hx
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
    exact hplacement _

def parseCoefficient (p : Source.Parameters) : ℝ :=
  ((shapeConstant shape+12 : ℕ) : ℝ)*(widthCoefficient p+1)*descriptionBitCoefficient p

theorem parse_cost_polynomial (hm2 : 2≤S.nnz) (hp : Source.Promises p S) (hb : S.source≠0)
    (j : Fin (drawCount p S hm)) :
    (skipPrice shape (data p S hm j) : ℝ)≤parseCoefficient p*
      (S.nnz : ℝ)^(3/2 : ℝ)*(logSize S : ℝ)^89 := by
  have hlen := wire_nonempty shape (data p S hm j)
  have hc := price_le shape (data p S hm j) _ (data_width p S hm hm2 hp hb j)
  have hskip : skipPrice shape (data p S hm j)≤(shapeConstant shape+12)*
      (descriptionBits p S hm j).length*(widthCoefficient p*(logSize S)^25+1) := by
    rw [data_wire,chronologicalDescriptionBits_length] at hlen hc
    dsimp [skipPrice]
    rw [data_wire,chronologicalDescriptionBits_length]
    nlinarith only [hc,hlen,Nat.zero_le
      ((descriptionBits p S hm j).length*widthCoefficient p*(logSize S)^25)]
  have hℓ : (1:ℝ)≤logSize S := by exact_mod_cast Parameters.inputLog_pos S.nnz
  have hword : (widthCoefficient p:ℝ)*(logSize S:ℝ)^25+1≤
      (widthCoefficient p+1)*(logSize S:ℝ)^25 := by
    have := one_le_pow₀ hℓ (n:=25)
    nlinarith only [this]
  have hd := descriptionBits_polynomial p S hm hm2 hp hb j
  have hd0 : 0≤descriptionBitCoefficient p*(S.nnz:ℝ)^(3/2:ℝ)*(logSize S:ℝ)^64 :=
    (Nat.cast_nonneg _).trans hd
  have hr : (skipPrice shape (data p S hm j):ℝ)≤(shapeConstant shape+12 : ℕ)*
      ((descriptionBits p S hm j).length:ℝ)*((widthCoefficient p:ℝ)*(logSize S:ℝ)^25+1) := by
    exact_mod_cast hskip
  have hc0 : (0:ℝ)≤(shapeConstant shape+12 : ℕ) := Nat.cast_nonneg _
  have hw0 : (0:ℝ)≤(widthCoefficient p:ℝ)*(logSize S:ℝ)^25+1 :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)) (by norm_num)
  calc
    _≤(shapeConstant shape+12 : ℕ)*
        (descriptionBitCoefficient p*(S.nnz:ℝ)^(3/2:ℝ)*(logSize S:ℝ)^64)*
        ((widthCoefficient p+1)*(logSize S:ℝ)^25) := by
      exact hr.trans (mul_le_mul (mul_le_mul_of_nonneg_left hd hc0) hword hw0 (mul_nonneg hc0 hd0))
    _=_ := by unfold parseCoefficient;ring

#print axioms data_width
#print axioms parse_cost_polynomial

end Maxwell.Continuum.DescriptionSchema
