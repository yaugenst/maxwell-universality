import Maxwell.Continuum.CalibrationBasisForcingReset
import Maxwell.Continuum.NaturalBankImportWord

/-! One complete runtime source-array iteration: reset scratch, import the
padded countdown, decode the alias, compute the forcing value, and store it. -/
namespace Maxwell.Continuum.Calibration.BasisForcing
open Maxwell.Cost Maxwell.Cost.Structured FreeFiber RationalDataflow PartArray
open ArrayDecodeMachine
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 2048

def inputNaturals (n : ℕ → ℕ) (v : ℕ → Parts) (row : ℕ) : ℕ → ℕ :=
  Function.update (clearedNaturals n v) 310 row
def bodyCode (column : Fin 24) : Code :=
  .seq resetCode (.seq (NaturalImport.code 201 310) (storeCode column))
def bodyCost (B W : ℕ) : ℕ := 2^660*(prepareWidth B+W+10)^2
attribute [local irreducible] bank clearRegisters prepareCode storeCode resetCode

theorem input_agrees (n : ℕ → ℕ) (v : ℕ → Parts) (row k : ℕ) (hk : k∈ids bank) :
    inputNaturals n v row k=dataValues (clearedParts v) k := by
  have he : k≠310 := fun h => (outside_bank 310 (by decide) (by decide)) (h ▸ hk)
  rw [inputNaturals,Function.update_of_ne he,clearedNaturals_agrees n v k hk]

theorem input_radius (n : ℕ → ℕ) (v : ℕ → Parts) (row : ℕ) : inputNaturals n v row 311=n 311 := by
  rw [inputNaturals,Function.update_of_ne (by decide : (311:ℕ)≠310),clearedNaturals_radius]

theorem input_work (n : ℕ → ℕ) (v : ℕ → Parts) (row k : ℕ) (hk : k∈NaturalQuotient.workPorts) :
    inputNaturals n v row k=0 := by
  have he : k≠310 := by
    simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hk
    omega
  rw [inputNaturals,Function.update_of_ne he,clearedNaturals_work n v k hk]

theorem body_executes (column : Fin 24) (n : ℕ → ℕ) (v : ℕ → Parts)
    (hn : ∀k∈ids bank,n k=dataValues v k) (hg : Good bank v)
    (B W : ℕ) (hB : 103≤B) (hw : ∀k∈naturalIds,(n k).bits.length≤prepareWidth B)
    (hv : ∀k∈retained,(v k).Width B)
    (R : ℕ) (i : Fin (aliasArraySize R)) (hR : n 311=R) (hRadius : R.bits.length≤B)
    (a : Table (aliasArraySize R)) (hm : a.MetadataWidth W)
    (hfit : 625≤addressValue a.width) (hsep : a.Separated)
    (input : List Bool) (tape : ℕ → Bool) (xs : List Bool) (hlen : xs.length≤B)
    (hindex : addressValue xs=i.val) (s : Store) (hs : NatAssign.Bank naturalIds n s.val)
    (hz : ∀k,k<5 → RationalAccumulator.Blank s.val k) (ha : a.OutputReady s)
    (hx : BankArray.Word s.val 201 xs) :
    ∃cost t out,Executes input tape (bodyCode column) cost s t ∧ cost≤bodyCost B W ∧
      Good bank out ∧ WidthBank bank (prepareWidth B) out ∧ (out 32).Width 625 ∧
      NatAssign.Bank naturalIds (preparedNaturals (inputNaturals n v i.val) out) t.val ∧
      (∀k∈naturalIds,(preparedNaturals (inputNaturals n v i.val) out k).bits.length≤prepareWidth B) ∧
      (a.set i (out 32)).OutputReady t ∧
      (out 32).value=rationalRightCoupling (rationalBasisField column)
        (arrayAliasAt R i) (arrayPolarizationAt R i) ∧
      (∀k∈retained,out k=v k) ∧
      (∀k,k<5 → RationalAccumulator.Blank t.val k) ∧
      t.val.tapes 201=s.val.tapes 201 ∧
      t.val.inputHead=s.val.inputHead ∧ t.val.randomCursor=s.val.randomCursor ∧ t.val.output=s.val.output ∧ SourceFrame s.val t.val := by
  have hBU : B≤prepareWidth B := by unfold prepareWidth;omega
  obtain ⟨c0,u,e0,hc0,r0,g0,w0,b0,nw0,z0,f0⟩ := reset_executes n v (prepareWidth B) B (by omega) hBU
    hn hw hg hv (by simpa only [hR] using hRadius) input tape s hs hz
  have word : BankArray.Word u.val 201 xs := BankArray.word_of_eq
    (f0.tapes 201 (protected_external 201 (by simp [protectedPorts]))) hx
  obtain ⟨c1,u1,e1,hc1,b1,f1⟩ := NaturalImport.executes naturalIds 201 310 (naturalIds_decode (by decide))
    (by decide) (clearedNaturals n v) xs input tape u b0 word
  rw [hindex] at b1
  have indexWidth : i.val.bits.length≤B := by
    rw [← hindex,Nat.size_eq_bits_len]
    exact (Nat.size_le.mpr (Subtraction.addressValue_lt_pow_length xs)).trans hlen
  have nw1 : ∀k∈naturalIds,(inputNaturals n v i.val k).bits.length≤B :=
    nat_update_width (clearedNaturals n v) naturalIds B 310 i.val nw0 indexWidth
  have z1 (k : ℕ) (hk : k<5) : RationalAccumulator.Blank u1.val k :=
    RationalAccumulator.blank_of_eq (f1.tapes k (by simp only [Finset.mem_singleton];omega)) (z0 k hk)
  have r1 : Ready bank (clearedParts v) u1 := ⟨fun k hk => by
    have hh := b1 k (naturalIds_parts hk)
    change RationalAccumulator.Word u1.val k (inputNaturals n v i.val k) at hh
    rwa [input_agrees n v i.val k hk] at hh,fun k hk => z1 k (by omega)⟩
  have f1' : BinaryPrecision.Frame changed u.val u1.val := f1.mono (by
    intro k hk
    have he : k=310 := by simpa only [Finset.mem_singleton] using hk
    subst k
    exact Finset.mem_union_right _ (naturalIds_decode (by decide)))
  have frame := f0.trans f1'
  have output := output_frame a s u1 ha (clearedParts v) r1 frame
  obtain ⟨c2,t,out,e2,hc2,_,g2,w2,entryWidth,b2,nw2,oa,value,keep,z2,_,counter,ih,random,emitted,continuation⟩ :=
    store_executes column (inputNaturals n v i.val) (clearedParts v) (input_agrees n v i.val)
      (input_work n v i.val) g0 B W hB nw1 R i ((input_radius n v i.val).trans hR)
      (by simp only [inputNaturals,Function.update_self]) a hm hfit hsep input tape u1 b1 z1 output
  refine ⟨c0+(c1+c2),t,out,e0.seq (e1.seq e2),?_,g2,w2,entryWidth,b2,nw2,oa,value,?_,z2,
    counter.trans (frame.tapes 201 (protected_external 201 (by simp [protectedPorts]))),
    ih.trans frame.inputHead,random.trans frame.randomCursor,emitted.trans frame.output,fun k hk => (continuation k hk).trans (frame.tapes k (continuation_outside k hk).2.1)⟩
  · have old := nw0 310 (naturalIds_decode (by decide))
    have sq0 : (prepareWidth B+3)^2≤(prepareWidth B+W+10)^2 := Nat.pow_le_pow_left (by omega) 2
    have sq1 : (B+5)^2≤(prepareWidth B+W+10)^2 := Nat.pow_le_pow_left (by omega) 2
    have sq2 : (max B W+5)^2≤(prepareWidth B+W+10)^2 := Nat.pow_le_pow_left (by
      have hmax : max B W≤prepareWidth B+W := max_le (by omega) (by omega)
      omega) 2
    have linear : B+1≤(prepareWidth B+W+10)^2 :=
      (by omega : B+1≤prepareWidth B+W+10).trans (le_self_pow (by omega) (by decide : (2:ℕ)≠0))
    unfold bodyCost
    nlinarith only [hc0,hc1,hc2,old,hlen,sq0,sq1,sq2,linear]
  · intro k hk
    have hh := hk
    simp only [retained,Finset.mem_sdiff,Finset.mem_range,Finset.mem_insert,Finset.mem_singleton,not_or] at hh
    exact (keep k hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2).trans (clearedParts_keep v k hk)

#print axioms body_executes
end Maxwell.Continuum.Calibration.BasisForcing
