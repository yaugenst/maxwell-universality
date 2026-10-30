import Maxwell.Continuum.FiniteDecoderSetup
import Maxwell.Cost.DecoderParser.RuntimeBounds

namespace Maxwell.Continuum.FiniteDecoder
open Maxwell.Cost Maxwell.Cost.DecoderParser
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private theorem bits_length_le (n : ℕ) : n.bits.length≤n := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  exact Nat.lt_two_pow_self

theorem beforeRows_width {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (L : ℕ)
    (h : WidthBound descriptionShape (descriptionData D) L) :
    WidthBound headerShape (headerData D) L := h.1

theorem beforeRows_length {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) :
    (beforeRows D).length≤(description D).length := by
  rw [description_rows]
  simp only [List.length_append]
  omega

theorem setupPrice_bound {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (L : ℕ)
    (htarget : WidthBound descriptionShape (descriptionData D) L)
    (hW : D.format.width ≤ L) (hsamples : D.sampleCount.bits.length ≤ L)
    (hmessages : (D.sampleCount*D.format.width).bits.length ≤ L) :
    setupPrice D ≤ 100000*((description D).length+D.sampleCount*D.format.width+1)*(L+1)^2 := by
  let T := (description D).length
  let M := D.sampleCount*D.format.width
  have hn : n.bits.length ≤ L := htarget.1.1
  have hi : D.format.integerBits.bits.length ≤ L :=
    (bits_length_le _).trans (by unfold Target.FixedPointFormat.width at hW;omega)
  have hf : D.format.fractionalBits.bits.length ≤ L :=
    (bits_length_le _).trans (by unfold Target.FixedPointFormat.width at hW;omega)
  have hif : D.format.integerBits+D.format.fractionalBits ≤ L := by
    unfold Target.FixedPointFormat.width at hW;omega
  have hparse : retainedPrice D ≤ 542*T*(L+1) := by
    exact retainedPrice_bound D L htarget
  have hpref : price headerShape (headerData D) ≤ 271*T*(L+1) := by
    have hh := price_le headerShape (headerData D) L (beforeRows_width D L htarget)
    have hl := beforeRows_length D
    change _ ≤ 71*(beforeRows D).length*(L+1) at hh
    exact hh.trans (by gcongr; omega)
  have harith : MetadataProduct.costBound D.format.integerBits D.format.fractionalBits D.sampleCount ≤ 36000*(L+1)^2 := by
    unfold MetadataProduct.costBound
    calc
      _ ≤ 1000*(6*(L+1))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = _ := by ring
  have hconstants : DecoderConstants.costBound D.format.integerBits D.format.fractionalBits ≤ 50000*(L+1)^2 := by
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
  change retainedPrice D+(MetadataProduct.costBound _ _ _+LoadMessages.costBound M+
    Replay.costBound M.bits.length M T+(11*T+10+price headerShape (headerData D)))+
    DecoderConstants.costBound _ _+(20*n.bits.length+24)+(21*n.bits.length+16) ≤ _
  nlinarith only [hparse,hpref,harith,hconstants,hload,hrewind,htp,hmp,hcp,hraw,hsmall]

#print axioms setupPrice_bound

end Maxwell.Continuum.FiniteDecoder

