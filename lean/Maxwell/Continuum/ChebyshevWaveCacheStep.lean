import Maxwell.Continuum.ChebyshevWaveCacheLoad
import Maxwell.Continuum.ChebyshevWaveCacheValues

/-! One fully executed cache row: load the runtime index, compute both
rounded wave coefficients, and write their canonical integer channels. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
open RationalDataflow.PartArray
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def cacheStepCode : Code := .seq cacheLoadCode (.seq encodedCode cacheWriteCode)
def cacheStepCost (Q P grid W B : ℕ) : ℕ :=
  cacheLoadCost B W grid+encodedCost Q P grid W+rowPlanCost 2 1 W cacheWritePlan

theorem cacheStep_executes {n : ℕ} (a : Table n) (q : ℚ) (Q N D W B : ℕ)
    (b : Table (2*D)) (hm : b.MetadataWidth W) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (hq : |q| ≤ Q) (hD : D ≤ waveDegree (8*Q) N+1)
    (hfit : waveWorkBits (8*Q) N+7 ≤ addressValue b.width)
    (v base : ℕ→Parts) (hbase : WidthBank ids W base) (hg : Good ids base)
    (hmeta : SameMetadata v base) (hw : WidthBank ids B v) (hW : 1 ≤ W)
    (hgrid : (waveGrid (8*Q) N).bits.length ≤ W)
    (hone : base 15=⟨1,0,1⟩) (hi : SumInput (waveGrid (8*Q) N) q 0 0 base)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (hlen : xs.length ≤ W)
    (hj : addressValue xs<D) (s : Store) (hs : LoopReady Q (waveWorkBits (8*Q) N) v s)
    (ha : a.Ready s) (hb : b.OutputReady s) (hindex : BankArray.Word s.val 201 xs)
    (hz : Blank s.val 680) (hgridWord : Word s.val 681 (waveGrid (8*Q) N))
    (hsaved : ∀i∈savedPorts,Blank s.val i) (hpower : Word s.val 144 (2^waveWorkBits (8*Q) N)) :
    ∃cost t,Executes input tape cacheStepCode cost s t ∧
      cost ≤ cacheStepCost Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) W B ∧
      let w := encodedValues Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) (cacheLoaded (addressValue xs) v)
      LoopReady Q (waveWorkBits (8*Q) N) w t ∧ a.Ready t ∧
      (cachePut q Q N (addressValue xs) b).OutputReady t ∧
      WidthBank ids (encodedWidth Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) W) w ∧
      SameMetadata w base ∧ Blank t.val 680 ∧ Word t.val 681 (waveGrid (8*Q) N) ∧
      (∀i∈savedPorts,Blank t.val i) ∧ Word t.val 144 (2^waveWorkBits (8*Q) N) ∧
      t.val.tapes 201=s.val.tapes 201 := by
  let P := waveWorkBits (8*Q) N
  let grid := waveGrid (8*Q) N
  let j := addressValue xs
  have hjbits : j.bits.length ≤ W := by
    have h : j.bits.length ≤ xs.length := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr (Subtraction.addressValue_lt_pow_length xs)
    exact h.trans hlen
  have hloaded := cacheLoaded_width j W v base hmeta hbase hW hjbits
  have gloaded := cacheLoaded_good j v base hmeta hg
  have iloaded := cacheLoaded_input grid j q v base hmeta hi
  obtain ⟨c0,s0,e0,hc0,r0,n0,f0⟩ := cacheLoad_executes Q P grid B v hw input tape xs s hs hindex hz hgridWord
  have f0e := f0.mono cacheLoad_subset_encoded
  have saved0 : ∀i∈savedPorts,Blank s0.val i := by
    intro i hi
    have hr := savedPorts_range i hi
    apply blank_of_eq (f0.tapes i _) (hsaved i hi)
    simp only [cacheLoadWorkspace,Finset.mem_insert]
    exact not_or_intro (by omega) (RationalDataflow.outside_workspace ids i (by omega))
  have grid0 := word_of_eq (f0e.tapes 681 (cache_preserved 681 (by decide))) hgridWord
  have power0 := word_of_eq (f0.tapes 144 (by decide)) hpower
  obtain ⟨c1,s1,e1,hc1,r1,z1,n1,saved1,power1,hw1,f1⟩ := encoded_executes Q P grid W _ hloaded gloaded
    hW hgrid (cacheLoaded_counter j v) (cacheLoaded_one j v base hmeta hone)
    input tape s0 r0 n0 grid0 saved0 power0
  have f01 := f0e.trans f1
  have ar := Table.Ready.wave_frame ha f01 r1.ready.2
  have br := Table.OutputReady.wave_frame hb f01 r1.ready.2
  have index1 := BankArray.word_of_eq (f01.tapes 201 (cache_preserved 201 (by decide))) hindex
  have result := encodedValues_wave q Q N j _ gloaded iloaded
    (cacheLoaded_zero j v 8 (by decide)) (cacheLoaded_zero j v 9 (by decide))
  let w := encodedValues Q P grid (cacheLoaded j v)
  change w 8=waveCacheReal q Q N j ∧ w 9=waveCacheImag q Q N j at result
  have fits := encodedValues_wave_width q Q N j hq (by dsimp [j];omega) _ gloaded iloaded
    (cacheLoaded_zero j v 8 (by decide)) (cacheLoaded_zero j v 9 (by decide))
  obtain ⟨c2,t,e2,hc2,r2,at',bt,zt,ft⟩ := rowWritePlan_executes a b ids 2 1 W cacheWritePlan
    (by simp [cacheWritePlan,ids]) (by simp [cacheWritePlan]) hm w
    (by intro x hx; simp only [cacheWritePlan,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact fits.1.mono hfit
        · exact fits.2.mono hfit)
    (by omega) hsep hdisjoint input tape xs hlen
    (by intro x hx; simp only [cacheWritePlan,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> omega)
    s1 r1.ready ar br index1 (fun i hi => r1.floor.2 i (by
      simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
      simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton]
      omega))
  have lr2 := r1.rowWrite_frame ft r2 (e2.protectsTape 4 cacheWrite_protects_four) zt
  have tableEq : rowWriteTable 2 j cacheWritePlan w b=cachePut q Q N j b := by
    change (b.setD (2*j) (w 8)).setD (2*j+1) (w 9)=
      (b.setD (2*j) (waveCacheReal q Q N j)).setD (2*j+1) (waveCacheImag q Q N j)
    rw [result.1,result.2]
  rw [tableEq] at bt
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,lr2,at',bt,hw1,?_,
    blank_of_eq (ft.tapes 680 (by decide) (by decide) (by decide)) z1,
    word_of_eq (ft.tapes 681 (by decide) (by decide) (by decide)) n1,?_,
    word_of_eq (ft.tapes 144 (by decide) (by decide) (by decide)) power1,
    ft.counter.trans (f01.tapes 201 (cache_preserved 201 (by decide)))⟩
  · have hc0' : c0 ≤ cacheLoadCost B W grid := hc0.trans (by unfold cacheLoadCost;omega)
    change c0+(c1+c2) ≤ cacheLoadCost B W grid+encodedCost Q P grid W+rowPlanCost 2 1 W cacheWritePlan
    omega
  · intro i hi
    exact (encodedValues_metadata Q P grid _ i hi).trans
      ((cacheLoaded_metadata j v i hi).trans (hmeta i hi))
  · intro i hi
    have hh := savedPorts_range i hi
    apply blank_of_eq (ft.tapes i (by omega) (by omega) _) (saved1 i hi)
    simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton]
    omega

#print axioms cacheStep_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
