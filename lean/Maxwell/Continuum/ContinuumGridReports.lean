import Maxwell.Continuum.ContinuumAmbientEncoding
import Maxwell.Continuum.ContinuumRawReports

/-! Explicit addresses for continuum reports. A well uses its three emitted
integer center coordinates. Empty grid slots carry the zero test, so no
enumeration oracle for the decorated vertex type enters the decoder. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace Maxwell.Continuum.FiniteAuxiliary

def reportFormat (R P : ℕ) : Target.FixedPointFormat := ⟨R+2,P⟩

def reportFormatWord (R P : ℕ) (w : (reportFormat R P).Word) : Fin (2^(R+P+3)) :=
  ⟨w.val,by
    have h := w.isLt
    have he : (reportFormat R P).width=R+P+3 := by
      simp only [reportFormat,Target.FixedPointFormat.width]
      omega
    exact h.trans_eq (congrArg (fun n : ℕ => 2^n) he)⟩

theorem reportFormatWord_value (R P : ℕ) (w : (reportFormat R P).Word) :
    (momentWordDyadic P (R+P+2) (reportFormatWord R P w)).value=(reportFormat R P).value w := by
  simp only [momentWordDyadic,Maxwell.Dyadic.value,reportFormatWord,reportFormat,
    Target.FixedPointFormat.value,Target.FixedPointFormat.numerator]
  rw [show R+P+2=R+2+P by omega]

end Maxwell.Continuum.FiniteAuxiliary

namespace Maxwell.Continuum.RealizationParameters
open Maxwell.Composition FiniteAuxiliary
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent computedEnclosures strengthData momentPrecision messageRangeBits

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

def gridSide (k : Fin 3) : ℕ := Parameters.sourcePhysicalLengths p S hm k+1

def gridCount : ℕ := gridSide p S hm 0*(gridSide p S hm 1*gridSide p S hm 2)

def gridCoordinate (i : SourceDecoration.Vertex S (precision p S hm)) (k : Fin 3) :
    Fin (gridSide p S hm k) :=
  ⟨(integerCenter p S hm i k).toNat,by
    have hi := integerCenter_bounds p S hm i k
    unfold gridSide
    omega⟩

def gridAddress (i : SourceDecoration.Vertex S (precision p S hm)) : Fin (gridCount p S hm) :=
  finProdFinEquiv (gridCoordinate p S hm i 0,
    finProdFinEquiv (gridCoordinate p S hm i 1,gridCoordinate p S hm i 2))

theorem gridAddress_injective : Function.Injective (gridAddress p S hm) := by
  intro i j h
  have hpair := finProdFinEquiv.injective h
  have htail := finProdFinEquiv.injective (congrArg Prod.snd hpair)
  have hc (k : Fin 3) : gridCoordinate p S hm i k=gridCoordinate p S hm j k := by
    fin_cases k
    · exact congrArg Prod.fst hpair
    · exact congrArg Prod.fst htail
    · exact congrArg Prod.snd htail
  apply Parameters.sourceCell_injective p S hm (stage p S hm)
  funext k
  have hn := congrArg (fun x : Fin (gridSide p S hm k) => (x.val : ℤ)) (hc k)
  have hi := (integerCenter_bounds p S hm i k).1
  have hj := (integerCenter_bounds p S hm j k).1
  change ((integerCenter p S hm i k).toNat : ℤ)=((integerCenter p S hm j k).toNat : ℤ) at hn
  rw [Int.toNat_of_nonneg hi,Int.toNat_of_nonneg hj] at hn
  unfold integerCenter at hn
  omega

theorem gridCount_ambient : gridCount p S hm≤8*(ambientCells p S hm).length := by
  have hs (k : Fin 3) : gridSide p S hm k≤2*Parameters.sourcePhysicalLengths p S hm k := by
    have hp := Parameters.sourcePhysicalLengths_pos p S hm k
    unfold gridSide
    omega
  have h := Nat.mul_le_mul (hs 0) (Nat.mul_le_mul (hs 1) (hs 2))
  change gridCount p S hm≤_ at h
  simp only [ambientCells,AmbientEncoding.cubes_length]
  exact h.trans_eq (by ring)

theorem gridSide_binary (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) (k : Fin 3) :
    gridSide p S hm k≤2^(scaleBits p S+1) := by
  have h := (physical_side_le_count p S hm k).trans (count_binary p S hm hm2 hu)
  have hp : 0<2^scaleBits p S := by positivity
  unfold gridSide
  rw [pow_succ]
  omega

theorem gridCount_binary (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    gridCount p S hm≤2^(3*(scaleBits p S+1)) := by
  have h := Nat.mul_le_mul (gridSide_binary p S hm hm2 hu 0)
    (Nat.mul_le_mul (gridSide_binary p S hm hm2 hu 1) (gridSide_binary p S hm hm2 hu 2))
  change gridCount p S hm≤_ at h
  rw [← pow_add,← pow_add] at h
  convert h using 1
  congr 1
  omega

theorem gridCount_word_bits (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    Maxwell.unsignedBitLength (gridCount p S hm)≤(3*analysisBits p+4)*logSize S := by
  have h := Maxwell.Codec.unsignedBitLength_mono (gridCount_binary p S hm hm2 hu)
  rw [Maxwell.Dyadic.denominator_bitLength] at h
  have hℓ := Parameters.inputLog_pos S.nnz
  change 0<logSize S at hℓ
  unfold scaleBits at h
  nlinarith only [h,hℓ]

def gridTemplate (q : Fin (gridCount p S hm)) :=
  if h : ∃i,gridAddress p S hm i=q then selectedTemplates p S hm h.choose else 0

theorem gridTemplate_address (i : SourceDecoration.Vertex S (precision p S hm)) :
    gridTemplate p S hm (gridAddress p S hm i)=selectedTemplates p S hm i := by
  unfold gridTemplate
  split
  next h => rw [gridAddress_injective p S hm h.choose_spec]
  next h => exact False.elim (h ⟨i,rfl⟩)

def gridReportFormat : Target.FixedPointFormat :=
  reportFormat (messageRangeBits (inverseBound p S hm) S.nnz) (momentPrecision p S)

def gridReportWord (w : (gridReportFormat p S hm).Word) : RawReportWord p S hm :=
  reportFormatWord _ _ w

theorem gridReportWord_value (w : (gridReportFormat p S hm).Word) :
    (rawReportDyadic p S hm (gridReportWord p S hm w)).value=
      (gridReportFormat p S hm).value w :=
  reportFormatWord_value _ _ w

def gridRawReports (w : Fin (gridCount p S hm) → (gridReportFormat p S hm).Word) :
    SourceDecoration.Vertex S (precision p S hm) → RawReportWord p S hm :=
  fun i => gridReportWord p S hm (w (gridAddress p S hm i))

#print axioms gridAddress_injective
#print axioms gridCount_ambient
#print axioms gridCount_word_bits
#print axioms gridTemplate_address
#print axioms gridReportWord_value

end Maxwell.Continuum.RealizationParameters
