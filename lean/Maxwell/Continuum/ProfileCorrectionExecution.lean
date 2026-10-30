import Maxwell.Continuum.ProfileCorrectionInvariant

/-! Fixed-code correction and scaling of every stored profile coefficient.
All array reads, decisions, arithmetic, writes and countdowns are charged. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def correctionMapCode : Code := PartArray.mapCode correctionControl 1
def correctionMapTable {n : ℕ} (a b : PartArray.Table n) (v : ℕ→Parts) : PartArray.Table n :=
  b.filled (PartArray.mapValues a correctionControl 1 v) 0
def correctionMapCost (n B len : ℕ) : ℕ :=
  (n+1)*(13*len+15)+n*PartArray.mapStepCost correctionControl (correctionWorkingWidth n B)

theorem correction_map_executes {n : ℕ} (a b : PartArray.Table n) (B : ℕ) (hB : 1≤B)
    (ha : ∀i,(a.get i).Width B) (hav : ∀i,(a.get i).Valid)
    (v : ℕ→Parts) (hg : Good dftRegisters v)
    (hw : WidthBank dftRegisters (correctionWorkingWidth n B) v)
    (hconst : ∀i∈correctionConstants,(v i).Width B) (h7 : v 7=Parts.literal 1)
    (h8w : (v 8).Width B) (h8v : (v 8).value=n)
    (ham : a.MetadataWidth (correctionWorkingWidth n B))
    (hbm : b.MetadataWidth (correctionWorkingWidth n B))
    (hslot : correctionWorkingWidth n B≤addressValue b.width)
    (hsep : b.Separated) (hdis : a.SeparatedFrom b)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤correctionWorkingWidth n B) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : SharedConversion.Ready dftRegisters v s) (hat : a.Ready s) (hbt : b.OutputReady s) :
    ∃cost t finalWord,Executes input tape correctionMapCode cost s t ∧
      cost≤correctionMapCost n B xs.length ∧
      SharedConversion.Ready dftRegisters (correctionValues a v n) t ∧ a.Ready t ∧
      (correctionMapTable a b v).OutputReady t ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length ∧
      ∀i:Fin n,((correctionMapTable a b v).get i).Valid ∧
        ((correctionMapTable a b v).get i).Width (correctionWorkingWidth n B) ∧
        ((correctionMapTable a b v).get i).value=
          correctedValue (v 0).value (v 3).value (v 6).value (a.get i).value i.val := by
  have inv (k : ℕ) (hk : k≤n) := correction_invariant a v B hB ha hav hg hw hconst h7 h8w h8v k hk
  obtain ⟨cost,t,word,e,hc,r,at',bt',count,len⟩ := PartArray.map_executes a b dftRegisters (by decide)
    correctionControl correctionControl_valid 1 (by decide) v (correctionWorkingWidth n B)
    (by unfold correctionWorkingWidth;omega) ham hbm hslot hsep hdis
    (fun k hk => (inv k hk.le).width)
    (fun k hk => correctionLoaded_trace (inv k hk.le) hk hB ha hconst h7)
    (fun k hk => correctionLoaded_good (inv k hk.le) hav)
    (fun _ _ => correctionControl_admissible _) input tape xs origin hlen s hn hcount hs hat hbt
  refine ⟨cost,t,word,e,hc,r,at',bt',count,len,?_⟩
  have fit (i : Fin n) : (PartArray.mapValues a correctionControl 1 v i).Width (addressValue b.width) :=
    ((inv (n-i.val) (by omega)).width 1 (by decide)).mono hslot
  intro i
  rw [correctionMapTable,PartArray.Table.filled_get b _ fit]
  refine ⟨(inv (n-i.val) (by omega)).good 1 (by decide),
    (inv (n-i.val) (by omega)).width 1 (by decide),?_⟩
  let k := n-1-i.val
  have hk : k<n := by dsimp [k];have := i.isLt;omega
  have hnext : k+1=n-i.val := by dsimp [k];have := i.isLt;omega
  have hi : n-1-k=i.val := by dsimp [k];have := i.isLt;omega
  have he := correctionValues_output a v B k hk (inv k hk.le) hav h7
  rw [hnext,hi] at he
  simpa only [correctionValues,PartArray.mapValues,PartArray.Table.getD,dite_eq_left i.isLt] using he

theorem correctedValue_profile (N j : ℕ) :
    correctedValue (endpointInteger N).value (slopeInteger N).value
      ((2:ℚ)^profileWorkBits N)⁻¹ ((roundedCoefficient N j).numerator:ℚ) j=
      (encodedCoefficient N j).value := by
  rw [endpointInteger_value,slopeInteger_value]
  unfold correctedValue encodedCoefficient matchedCoefficient Dyadic.value
  split_ifs <;> push_cast <;> ring

#print axioms correction_map_executes
#print axioms correctedValue_profile
end Maxwell.Continuum.Profile.Runtime
