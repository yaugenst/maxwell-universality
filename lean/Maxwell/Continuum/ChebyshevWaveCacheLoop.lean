import Maxwell.Continuum.ChebyshevWaveCacheStep
import Maxwell.Continuum.RationalDataflowSizedCounted
import Maxwell.Continuum.RationalDataflowSharedPassFrame

/-! The complete fixed runtime loop populating the wave cache. All body
semantics, widths, table writes and countdown cleanup are discharged. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
open RationalDataflow.PartArray
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def cacheBankWidth (Q P grid W : ℕ) : ℕ := W+encodedWidth Q P grid W
def cacheCode : Code := .seq (countedProgram 201 cacheStepCode) (.call (TapeOps.clear 201))
def cacheCost (Q P grid D W : ℕ) : ℕ :=
  (D+1)*(13*D.bits.length+15)+D*cacheStepCost Q P grid W (cacheBankWidth Q P grid W)+
    6*D.bits.length+4

structure CacheState {n : ℕ} (a : Table n) (q : ℚ) (Q N D W : ℕ)
    (base : ℕ→Parts) (initial : Table (2*D)) (remaining : ℕ) (s : Store) where
  remaining_le : remaining ≤ D
  values : ℕ→Parts
  table : Table (2*D)
  ready : LoopReady Q (waveWorkBits (8*Q) N) values s
  bankWidth : WidthBank ids
    (cacheBankWidth Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) W) values
  metadata : SameMetadata values base
  source : a.Ready s
  output : table.OutputReady s
  tableMetadata : CacheTableMetadata table initial
  contents : CacheContents q Q N D remaining table
  innerBlank : Blank s.val 680
  grid : Word s.val 681 (waveGrid (8*Q) N)
  saved : ∀i∈savedPorts,Blank s.val i
  power : Word s.val 144 (2^waveWorkBits (8*Q) N)

theorem CacheState.count_frame {n Q N D W r : ℕ} {a : Table n} {q : ℚ}
    {base : ℕ→Parts} {initial : Table (2*D)} {s t : Store}
    (h : CacheState a q Q N D W base initial r s) (f : CountedShifted.Frame 201 s t) :
    Nonempty (CacheState a q Q N D W base initial r t) := by
  have keep (i : ℕ) (hi : i≠201) := f.2.2.2.2.2.1 i hi
  refine ⟨{ h with
    ready := h.ready.count201_frame f
    source := h.source.count_frame f
    output := h.output.count_frame f
    innerBlank := blank_of_eq (keep 680 (by decide)) h.innerBlank
    grid := word_of_eq (keep 681 (by decide)) h.grid
    saved := ?_
    power := word_of_eq (keep 144 (by decide)) h.power }⟩
  intro i hi
  have hh := savedPorts_range i hi
  exact blank_of_eq (keep i (by omega)) (h.saved i hi)

theorem LoopReady.outer_copy_frame {Q P : ℕ} {v : ℕ→Parts} {s t : Store}
    (h : LoopReady Q P v s) (f : WordReplace.Frame 201 s.val t.val) : LoopReady Q P v t := by
  have keep (i : ℕ) (hi : i≠201) := f.2.2.2.2.2.1 i hi
  refine ⟨h.ready.wordReplace_frame (RationalDataflow.outside_workspace ids 201 (by decide)) f,
    ?_,⟨?_,?_⟩,?_,word_of_eq (keep 652 (by decide)) h.rangeWord,
    word_of_eq (keep 653 (by decide)) h.precisionWord⟩
  · intro i hi
    have hip : i∈PhaseMachine.Runtime.ids := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
    have hn : i≠201 := by intro he;subst i;exact (by decide : 201∉PhaseMachine.Runtime.ids) hip
    exact blank_of_eq (keep i hn) (h.phase i hi)
  · exact blank_of_eq (keep 4 (by decide)) h.floor.1
  · intro i hi
    have hn : i≠201 := by
      simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    exact blank_of_eq (keep i hn) (h.floor.2 i hi)
  · intro i hi
    have hh := parameterIds_range i hi
    exact word_of_eq (keep i (by omega)) (h.parameters i hi)

theorem CacheState.copy_frame {n Q N D W r : ℕ} {a : Table n} {q : ℚ}
    {base : ℕ→Parts} {initial : Table (2*D)} {s t : Store}
    (h : CacheState a q Q N D W base initial r s) (f : WordReplace.Frame 201 s.val t.val) :
    Nonempty (CacheState a q Q N D W base initial r t) := by
  have keep (i : ℕ) (hi : i≠201) := f.2.2.2.2.2.1 i hi
  have ht := h.source.copy_frame (Or.inl rfl) f
  refine ⟨{ h with
    ready := h.ready.outer_copy_frame f
    source := ht
    output := h.output.copy_frame (Or.inl rfl) f ht.scratch ht.seven
    innerBlank := blank_of_eq (keep 680 (by decide)) h.innerBlank
    grid := word_of_eq (keep 681 (by decide)) h.grid
    saved := ?_
    power := word_of_eq (keep 144 (by decide)) h.power }⟩
  intro i hi
  have hh := savedPorts_range i hi
  exact blank_of_eq (keep i (by omega)) (h.saved i hi)

theorem cache_executes {n : ℕ} (a : Table n) (q : ℚ) (Q N D W : ℕ)
    (b : Table (2*D)) (hm : b.MetadataWidth W) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (hq : |q| ≤ Q) (hD : D ≤ waveDegree (8*Q) N+1)
    (hfit : waveWorkBits (8*Q) N+7 ≤ addressValue b.width)
    (base : ℕ→Parts) (hbase : WidthBank ids W base) (hg : Good ids base)
    (hW : 1 ≤ W) (hgrid : (waveGrid (8*Q) N).bits.length ≤ W) (hcount : D.bits.length ≤ W)
    (hone : base 15=⟨1,0,1⟩) (hi : SumInput (waveGrid (8*Q) N) q 0 0 base)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : LoopReady Q (waveWorkBits (8*Q) N) base s)
    (ha : a.Ready s) (hb : b.OutputReady s) (hn : Word s.val 201 D)
    (hz : Blank s.val 680) (hgridWord : Word s.val 681 (waveGrid (8*Q) N))
    (hsaved : ∀i∈savedPorts,Blank s.val i) (hpower : Word s.val 144 (2^waveWorkBits (8*Q) N)) :
    ∃cost t,Executes input tape cacheCode cost s t ∧
      cost ≤ cacheCost Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) D W ∧
      Nonempty (CacheState a q Q N D W base b 0 t) ∧ Blank t.val 201 := by
  obtain ⟨origin,hn⟩ := hn
  let P := waveWorkBits (8*Q) N
  let grid := waveGrid (8*Q) N
  let B := cacheBankWidth Q P grid W
  let inv : ℕ→Store→Prop := fun r st => Nonempty (CacheState a q Q N D W base b r st)
  have initial : inv D s := ⟨{
    remaining_le := le_rfl
    values := base
    table := b
    ready := hs
    bankWidth := hbase.mono (by unfold cacheBankWidth;omega)
    metadata := fun _ _ => rfl
    source := ha
    output := hb
    tableMetadata := CacheTableMetadata.refl b
    contents := cacheContents_initial q Q N D b
    innerBlank := hz
    grid := hgridWord
    saved := hsaved
    power := hpower }⟩
  have stable : ∀r u v,CountedShifted.Frame 201 u v → inv r u → inv r v := by
    intro r u v f h
    obtain ⟨h⟩ := h
    exact h.count_frame f
  have body : ∀r xs u,inv (r+1) u → u.val.tapes 201=BitTape.shifted xs origin →
      addressValue xs=r → xs.length=D.bits.length →
      ∃cost t,Executes input tape cacheStepCode cost u t ∧ inv r t ∧
        t.val.tapes 201=BitTape.shifted xs origin ∧ cost ≤ cacheStepCost Q P grid W B := by
    intro r xs u hu hx hval hlen
    obtain ⟨hu⟩ := hu
    have hr : r<D := by have := hu.remaining_le;omega
    have hfit' : P+7 ≤ addressValue hu.table.width := by rw [hu.tableMetadata.width];exact hfit
    obtain ⟨c,t,e,hc,rt,at',bt,wt,mt,zt,gt,st,pt,ct⟩ := cacheStep_executes a q Q N D W B hu.table
      (hu.tableMetadata.widthBound hm) (hu.tableMetadata.separated hsep)
      (hu.tableMetadata.separatedFrom hdisjoint) hq hD hfit' hu.values base hbase hg hu.metadata
      hu.bankWidth hW hgrid hone hi input tape xs (by omega) (by omega) u hu.ready hu.source hu.output
      ⟨origin,hx⟩ hu.innerBlank hu.grid hu.saved hu.power
    have fits := waveRoundedCoefficient_bits q Q N r hq (by omega)
    have wf0 : (waveCacheReal q Q N r).Width (addressValue hu.table.width) :=
      (integer_literal_width _ _ fits.1 (by omega)).mono hfit'
    have wf1 : (waveCacheImag q Q N r).Width (addressValue hu.table.width) :=
      (integer_literal_width _ _ fits.2 (by omega)).mono hfit'
    refine ⟨c,t,e,?_,ct.trans hx,hc⟩
    refine ⟨{
      remaining_le := hr.le
      values := encodedValues Q P grid (cacheLoaded (addressValue xs) hu.values)
      table := cachePut q Q N r hu.table
      ready := rt
      bankWidth := wt.mono (by unfold cacheBankWidth;omega)
      metadata := mt
      source := at'
      output := ?_
      tableMetadata := (cachePut_metadata q Q N r hu.table).trans hu.tableMetadata
      contents := cacheContents_put q Q N D r hu.table hr hu.contents wf0 wf1
      innerBlank := zt
      grid := gt
      saved := st
      power := pt }⟩
    simpa only [hval] using bt
  obtain ⟨c0,s0,finalWord,e0,h0,w0,len0,_,hc0⟩ := counted_executes_sized 201 origin cacheStepCode input tape
    D.bits.length inv (fun _ => cacheStepCost Q P grid W B) stable body D D.bits s
      (addressValue_bits _) hn rfl initial
  obtain ⟨t,e1,tapes1,f1⟩ := WordCall.clear 201 input tape finalWord origin s0 w0
  have wf1 : WordReplace.Frame 201 s0.val t.val :=
    ⟨f1.1,f1.2.1,f1.2.2.1,f1.2.2.2.1,f1.2.2.2.2.1,
      fun i hi => f1.2.2.2.2.2.1 i hi hi,
      fun i _ _ h26 h27 => f1.2.2.2.2.2.2 i h26 h27⟩
  obtain ⟨state0⟩ := h0
  refine ⟨c0+(6*finalWord.length+4),t,e0.seq e1,?_,state0.copy_frame wf1,?_⟩
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at hc0
    change c0+(6*finalWord.length+4) ≤ (D+1)*(13*D.bits.length+15)+
      D*cacheStepCost Q P grid W B+6*D.bits.length+4
    omega
  · refine ⟨origin+finalWord.length,?_⟩
    simp only [tapes1,Function.update_self]

#print axioms cache_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
