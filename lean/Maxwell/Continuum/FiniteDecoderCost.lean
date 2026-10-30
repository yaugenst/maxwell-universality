import Maxwell.Continuum.FiniteDecoder
import Maxwell.Continuum.FiniteDecoderSetupCost

namespace Maxwell.Continuum.FiniteDecoder
open Maxwell.Cost Maxwell.Cost.DecoderParser
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- A directly computed word-width bound from the emitted decoder description. -/
def executionWidth {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) : ℕ :=
  maxWidth descriptionShape (descriptionData D)+D.format.width+decoderWidth D+
    D.sampleCount.bits.length+(D.sampleCount*D.format.width).bits.length

private theorem rowWidth_le_decoderWidth {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (row : Row D.sampleCount) (h : row ∈ rows D) : rowWidth D.format row ≤ decoderWidth D := by
  unfold decoderWidth
  generalize rows D=rs at *
  induction rs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl|h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

private theorem terms_length_le_wire {N : ℕ} (terms : List (Fin N × ℚ)) :
    terms.length ≤ (terms.flatMap termWire).length := by
  induction terms with
  | nil => simp
  | cons x xs ih =>
    have hx : 1 ≤ (termWire x).length := by simp [termWire,Codec.nat];omega
    simp only [List.length_cons,List.flatMap_cons,List.length_append]
    omega

private theorem row_work_le_wire {N : ℕ} (row : Row N) :
    row.2.length+1 ≤ (rowWire row).length := by
  have hh := terms_length_le_wire row.2
  simp only [rowWire,List.length_append,Codec.nat,List.length_cons,List.length_replicate]
  omega

private theorem rows_work_le_wire {N : ℕ} (rs : List (Row N)) :
    (rs.map (fun row => row.2.length+1)).sum ≤ (rs.flatMap rowWire).length := by
  induction rs with
  | nil => simp
  | cons x xs ih =>
    have hx := row_work_le_wire x
    simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append]
    omega

private theorem rows_length_le_work {N : ℕ} (rs : List (Row N)) :
    rs.length ≤ (rs.map (fun row => row.2.length+1)).sum := by
  induction rs with
  | nil => simp
  | cons x xs ih => simp only [List.length_cons,List.map_cons,List.sum_cons];omega

/-- Literal near-linear cost in the complete stored decoder description plus the complete
raw message stream, times the square of the actual word-width bound. -/
theorem costCap_bound {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) :
    costCap D ≤ 320000*((description D).length+D.sampleCount*D.format.width+1)*
      (executionWidth D+1)^2 := by
  let L := executionWidth D
  let T := (description D).length
  let M := D.sampleCount*D.format.width
  have hbase : maxWidth descriptionShape (descriptionData D) ≤ L := by dsimp [L,executionWidth];omega
  have htarget : WidthBound descriptionShape (descriptionData D) L :=
    (maxWidth_correct descriptionShape (descriptionData D)).mono _ _ hbase
  have hW : D.format.width ≤ L := by dsimp [L,executionWidth];omega
  have hj : D.sampleCount.bits.length ≤ L := by dsimp [L,executionWidth];omega
  have hm : M.bits.length ≤ L := by dsimp [M,L,executionWidth];omega
  have hA : decoderWidth D ≤ L := by dsimp [L,executionWidth];omega
  have hsetup := setupPrice_bound D L htarget hW hj hm
  have hflat : ((rows D).flatMap rowWire).length ≤ T := by
    dsimp [T];rw [description_rows];simp only [List.length_append];omega
  have hwork : ((rows D).map (fun row => row.2.length+1)).sum ≤ T :=
    (rows_work_le_wire _).trans hflat
  have hn : n ≤ T := by
    have hh := (rows_length_le_work (rows D)).trans hwork
    simpa using hh
  have hnb : n.bits.length ≤ L := htarget.1.1
  have hrows : ((rows D).map
        (rowPrice D (zeroMessages D) (decoderWidth D))).sum ≤
      ((rows D).map (fun row => row.2.length+1)).sum*(210000*(L+1)^2) := by
    have hrow (row : Row D.sampleCount) (hr : row ∈ rows D) :=
      rowPrice_bound D (zeroMessages D) row (decoderWidth D) L hA hW hj
        ((rowWidth_le_decoderWidth D row hr).trans hA)
    clear hflat hwork
    generalize rows D=rs at *
    induction rs with
    | nil => simp
    | cons x xs ih =>
      have hx := hrow x (by simp)
      have ht := ih (by intro y hy;exact hrow y (by simp [hy]))
      simp only [List.map_cons,List.sum_cons]
      nlinarith only [hx,ht]
  have hrows' : ((rows D).map
      (rowPrice D (zeroMessages D) (decoderWidth D))).sum ≤ T*(210000*(L+1)^2) :=
    hrows.trans (Nat.mul_le_mul_right _ hwork)
  have hout : (n+1)*(13*n.bits.length+15) ≤ 28*(T+M+1)*(L+1)^2 := by
    have hp : 13*n.bits.length+15 ≤ 28*(L+1)^2 := by nlinarith only [hnb,Nat.zero_le L]
    have hh := Nat.mul_le_mul (show n+1 ≤ T+M+1 by omega) hp
    simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh
  have hrows'' : T*(210000*(L+1)^2) ≤ 210000*(T+M+1)*(L+1)^2 := by
    have hh := Nat.mul_le_mul_right (210000*(L+1)^2) (show T ≤ T+M+1 by omega)
    simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh
  change _ ≤ 320000*(T+M+1)*(L+1)^2
  unfold costCap
  change setupPrice D ≤ 100000*(T+M+1)*(L+1)^2 at hsetup
  nlinarith only [hsetup,hout,hrows',hrows'',Nat.zero_le ((T+M+1)*(L+1)^2)]

/-- Stored natural fields, format width and address lengths have one common
bound B; the stencil cardinality contributes only a fixed multiplicative
factor to the decoder's largest arithmetic word. -/
theorem executionWidth_bound {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (B K : ℕ)
    (htarget : maxWidth descriptionShape (descriptionData D) ≤ B)
    (hformat : D.format.width ≤ B)
    (hsamples : D.sampleCount.bits.length ≤ B)
    (hmessages : (D.sampleCount*D.format.width).bits.length ≤ B)
    (hoffset : ∀ i, Source.ShortRational B (D.offset i))
    (hweight : ∀ i j, j ∈ D.support i → Source.ShortRational B (D.weight i j))
    (hsupport : ∀ i, (D.support i).card ≤ K) :
    executionWidth D ≤ (5*K+6)*(B+1) := by
  have hh := decoderWidth_bound D B K hoffset hweight hsupport
  have hm := Nat.mul_le_mul_left K (show 3*D.format.width+2*B+5 ≤ 5*(B+1) by omega)
  unfold executionWidth
  nlinarith only [htarget,hformat,hsamples,hmessages,hh,hm,Nat.zero_le K]

/-- The complete deterministic cap is linear in input length and quadratic
in the common coefficient/address width for a fixed stencil size. -/
theorem costCap_bounded {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (B K : ℕ)
    (htarget : maxWidth descriptionShape (descriptionData D) ≤ B)
    (hformat : D.format.width ≤ B)
    (hsamples : D.sampleCount.bits.length ≤ B)
    (hmessages : (D.sampleCount*D.format.width).bits.length ≤ B)
    (hoffset : ∀ i, Source.ShortRational B (D.offset i))
    (hweight : ∀ i j, j ∈ D.support i → Source.ShortRational B (D.weight i j))
    (hsupport : ∀ i, (D.support i).card ≤ K) :
    costCap D ≤ 320000*((description D).length+D.sampleCount*D.format.width+1)*
      (5*K+7)^2*(B+1)^2 := by
  have hw := executionWidth_bound D B K htarget hformat hsamples hmessages hoffset hweight hsupport
  have hw' : executionWidth D+1 ≤ (5*K+7)*(B+1) := by nlinarith only [hw,Nat.zero_le B]
  have hh := (costCap_bound D).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw' 2))
  simpa only [mul_pow,Nat.mul_assoc] using hh

#print axioms costCap_bound
#print axioms costCap_bounded

end Maxwell.Continuum.FiniteDecoder

