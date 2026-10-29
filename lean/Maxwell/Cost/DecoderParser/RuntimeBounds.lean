import Maxwell.Cost.Decoder
import Maxwell.Cost.DecoderParser.TargetRun

namespace Maxwell.Cost.DecoderParser
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private theorem bits_length_le (n : ℕ) : n.bits.length ≤ n := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  exact Nat.lt_two_pow_self

private theorem termPrice_bound (F : Target.FixedPointFormat) (j : ℕ) (q : ℚ)
    (w : F.Word) (A L : ℕ) (hA : A ≤ L) (hW : F.width ≤ L) (hj : j.bits.length ≤ L)
    (ht : termWidth F q (Codec.word F w) ≤ L) :
    termPrice F j q (Codec.word F w) A ≤ 200000*(L+1)^2 := by
  have hwb : F.width.bits.length ≤ L := (bits_length_le _).trans hW
  have hc : (2^(F.integerBits+F.fractionalBits)).bits.length=F.width := by
    rw [Nat.size_eq_bits_len,Nat.size_pow]
    simp [Target.FixedPointFormat.width,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  have hq : q.num.natAbs.bits.length ≤ L ∧ q.den.bits.length ≤ L := by
    dsimp [termWidth] at ht
    omega
  have hfetch : DecoderFetch.costCap F.width.bits j.bits (2^(F.integerBits+F.fractionalBits)).bits ≤
      1000*(2*L+5)^2+L*(15*(3*L+1)+24)+4+40*(4*L+3) := by
    simp only [DecoderFetch.costCap,ArrayAccess.costCap,List.length_nil,Nat.add_zero,RationalAccumulator.address_bits,hc]
    have haddr : 1000*(F.width.bits.length+j.bits.length+5)^2 ≤ 1000*(2*L+5)^2 := by
      gcongr
      omega
    have hread : F.width*(15*(F.width.bits.length+j.bits.length+1+F.width)+24) ≤
        L*(15*(3*L+1)+24) := Nat.mul_le_mul hW (by omega)
    have hclean : 40*(F.width.bits.length+j.bits.length+F.width+F.width+3) ≤ 40*(4*L+3) := by omega
    omega
  have hacc : 20000*(A+termWidth F q (Codec.word F w)+2)^2 ≤ 80000*(L+1)^2 := by
    calc
      _ ≤ 20000*(L+L+2)^2 := by gcongr
      _ = _ := by ring
  unfold termPrice
  nlinarith only [hfetch,hacc,hj,hq.1,hq.2,Nat.zero_le L]

theorem termsPrice_bound {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (w : D.Messages)
    (terms : List (Fin D.sampleCount × ℚ)) (A L : ℕ)
    (hW : D.format.width ≤ L) (hj : D.sampleCount.bits.length ≤ L)
    (hwidth : A+termsWidth D w terms ≤ L) :
    termsPrice D w terms A ≤ terms.length*(200000*(L+1)^2) := by
  induction terms generalizing A with
  | nil => simp [termsPrice]
  | cons x xs ih =>
    have hw : A+termWidth D.format x.2 (Codec.word D.format (w x.1))+1+termsWidth D w xs ≤ L := by
      simpa [termsWidth,List.map_cons,List.sum_cons,Nat.add_assoc] using hwidth
    have htail := ih (A+termWidth D.format x.2 (Codec.word D.format (w x.1))+1) hw
    have hindex : x.1.val.bits.length ≤ L := by
      have hh := Nat.size_le_size x.1.isLt.le
      rw [← Nat.size_eq_bits_len,← Nat.size_eq_bits_len] at hh
      exact hh.trans hj
    have hterm := termPrice_bound D.format x.1.val x.2 (w x.1) A L (by omega) hW hindex (by omega)
    simp only [termsPrice,List.length_cons]
    nlinarith only [htail,hterm]

theorem rowPrice_bound {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (w : D.Messages)
    (row : Row D.sampleCount) (A L : ℕ) (hA : A ≤ L) (hW : D.format.width ≤ L)
    (hj : D.sampleCount.bits.length ≤ L) (hrow : rowWidth D.format row ≤ L) :
    rowPrice D w A row ≤ (row.2.length+1)*(210000*(L+1)^2) := by
  have hw := (rowWidth_le D w row).trans hrow
  have htp := termsPrice_bound D w row.2 (offsetWidth row.1) L hW hj hw
  have hnum : row.1.num.natAbs.bits.length ≤ L := by dsimp [offsetWidth] at hw;omega
  have hden : row.1.den.bits.length ≤ L := by dsimp [offsetWidth] at hw;omega
  have hcount : row.2.length ≤ L := by
    have hsum : row.2.length ≤ (row.2.map (fun x => formatTermWidth D.format x.2+1)).sum := by
      induction row.2 with
      | nil => simp
      | cons x xs ih => simp only [List.length_cons,List.map_cons,List.sum_cons];omega
    dsimp [rowWidth] at hrow
    omega
  have hcb : row.2.length.bits.length ≤ L := (bits_length_le _).trans hcount
  have hhead : 18*A+38*(row.1.num.natAbs.bits.length+row.1.den.bits.length)+21*row.2.length.bits.length+96 ≤ 115*L+96 := by omega
  have hemit : 11*row.2.length.bits.length+10+400*(3*(offsetWidth row.1+termsWidth D w row.2)+4) ≤ 1211*L+1610 := by omega
  have hcounter : (row.2.length+1)*(13*row.2.length.bits.length+15) ≤ (row.2.length+1)*(13*L+15) := by gcongr
  unfold rowPrice
  nlinarith only [hhead,hemit,hcounter,htp,Nat.zero_le L,Nat.zero_le row.2.length]

theorem beforeRows_width {n : ℕ} (I : Target.Instance n) (L : ℕ)
    (h : WidthBound targetShape (targetPayload I) L) :
    WidthBound beforeRowsShape (beforeRowsPayload I) L := by
  rcases h with ⟨hn,hx,hy,hz,hm,hs,ht,hi,hf,hc,_⟩
  exact ⟨hn,⟨hx,hy,hz,hm,hs,ht⟩,hi,hf,hc⟩

theorem beforeRows_length {n : ℕ} (I : Target.Instance n) :
    (beforeRows I).length ≤ (Codec.target I).length := by
  rw [target_rows]
  simp only [List.length_append]
  omega

theorem setupPrice_bound {n : ℕ} (I : Target.Instance n) (L : ℕ)
    (htarget : WidthBound targetShape (targetPayload I) L)
    (hW : I.decoder.format.width ≤ L) (hsamples : I.decoder.sampleCount.bits.length ≤ L)
    (hmessages : (I.decoder.sampleCount*I.decoder.format.width).bits.length ≤ L) :
    setupPrice I ≤ 100000*((Codec.target I).length+I.decoder.sampleCount*I.decoder.format.width+1)*(L+1)^2 := by
  let T := (Codec.target I).length
  let M := I.decoder.sampleCount*I.decoder.format.width
  have hn : n.bits.length ≤ L := htarget.1
  have hi : I.decoder.format.integerBits.bits.length ≤ L :=
    (bits_length_le _).trans (by unfold Target.FixedPointFormat.width at hW;omega)
  have hf : I.decoder.format.fractionalBits.bits.length ≤ L :=
    (bits_length_le _).trans (by unfold Target.FixedPointFormat.width at hW;omega)
  have hif : I.decoder.format.integerBits+I.decoder.format.fractionalBits ≤ L := by
    unfold Target.FixedPointFormat.width at hW;omega
  have hparse : retainedTargetPrice I ≤ 542*T*(L+1) := by
    exact retainedTargetPrice_bound I L htarget
  have hpref : price beforeRowsShape (beforeRowsPayload I) ≤ 271*T*(L+1) := by
    have hh := price_le beforeRowsShape (beforeRowsPayload I) L (beforeRows_width I L htarget)
    have hl := beforeRows_length I
    change _ ≤ 171*(beforeRows I).length*(L+1) at hh
    exact hh.trans (by gcongr; omega)
  have harith : MetadataProduct.costBound I.decoder.format.integerBits I.decoder.format.fractionalBits I.decoder.sampleCount ≤ 36000*(L+1)^2 := by
    unfold MetadataProduct.costBound
    calc
      _ ≤ 1000*(6*(L+1))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = _ := by ring
  have hconstants : DecoderConstants.costBound I.decoder.format.integerBits I.decoder.format.fractionalBits ≤ 50000*(L+1)^2 := by
    unfold DecoderConstants.costBound
    calc
      _ ≤ 2000*(5*(L+1))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = _ := by ring
  have hload : LoadMessages.costBound M ≤ 64*(M+1)*(L+1) := by
    have hb : M.bits.length ≤ L := hmessages
    unfold LoadMessages.costBound
    nlinarith only [hb,Nat.zero_le M,Nat.zero_le L]
  have hrewind : Replay.costBound M.bits.length M T ≤ 80*(M+1)*(L+1)+6*T := by
    have hb : M.bits.length ≤ L := hmessages
    unfold Replay.costBound
    nlinarith only [hb,Nat.zero_le M,Nat.zero_le L]
  have hp2 : L+1 ≤ (L+1)^2 := by nlinarith
  have hone : 1 ≤ (L+1)^2 := by nlinarith
  have htp : T*(L+1) ≤ (T+M+1)*(L+1)^2 := Nat.mul_le_mul (by omega) hp2
  have hmp : (M+1)*(L+1) ≤ (T+M+1)*(L+1)^2 := Nat.mul_le_mul (by omega) hp2
  have hcp : (L+1)^2 ≤ (T+M+1)*(L+1)^2 := Nat.le_mul_of_pos_left _ (by omega)
  have hraw : T ≤ (T+M+1)*(L+1)^2 := (show T ≤ T+M+1 by omega).trans (Nat.le_mul_of_pos_right _ (by omega))
  have hsmall : 41*n.bits.length+50 ≤ 91*(T+M+1)*(L+1)^2 := by
    have hlinear : L+1 ≤ (T+M+1)*(L+1)^2 := hp2.trans hcp
    nlinarith only [hn,hlinear]
  change _ ≤ 100000*(T+M+1)*(L+1)^2
  unfold setupPrice preparePrice Replay.loadCostBound MetadataProduct.loadCostBound
  change retainedTargetPrice I+(MetadataProduct.costBound _ _ _+LoadMessages.costBound M+
    Replay.costBound M.bits.length M T+(11*T+10+price beforeRowsShape (beforeRowsPayload I)))+
    DecoderConstants.costBound _ _+(20*n.bits.length+24)+(21*n.bits.length+16) ≤ _
  nlinarith only [hparse,hpref,harith,hconstants,hload,hrewind,htp,hmp,hcp,hraw,hsmall]

end Maxwell.Cost.DecoderParser
