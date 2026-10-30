import Maxwell.Continuum.ChebyshevWaveCacheFrame
import Maxwell.Continuum.RationalDataflowRowWriteValues

/-! Literal integer contents of the real/imaginary wave-coefficient cache. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
open RationalDataflow.PartArray
set_option maxHeartbeats 3000000

def waveCacheReal (q : ℚ) (Q N j : ℕ) : Parts :=
  Parts.literal ((waveRoundedCoefficient q Q N j).1.numerator:ℚ)
def waveCacheImag (q : ℚ) (Q N j : ℕ) : Parts :=
  Parts.literal ((waveRoundedCoefficient q Q N j).2.numerator:ℚ)
def cachePut {n : ℕ} (q : ℚ) (Q N j : ℕ) (b : Table n) : Table n :=
  (b.setD (2*j) (waveCacheReal q Q N j)).setD (2*j+1) (waveCacheImag q Q N j)

structure CacheTableMetadata {n : ℕ} (b base : Table n) : Prop where
  width : b.width=base.width
  basePositive : b.basePositive=base.basePositive
  baseNegative : b.baseNegative=base.baseNegative
  baseDenominator : b.baseDenominator=base.baseDenominator
  clock : b.clock=base.clock

theorem CacheTableMetadata.refl {n : ℕ} (b : Table n) : CacheTableMetadata b b := ⟨rfl,rfl,rfl,rfl,rfl⟩
theorem CacheTableMetadata.trans {n : ℕ} {a b c : Table n}
    (h : CacheTableMetadata a b) (g : CacheTableMetadata b c) : CacheTableMetadata a c :=
  ⟨h.width.trans g.width,h.basePositive.trans g.basePositive,h.baseNegative.trans g.baseNegative,
    h.baseDenominator.trans g.baseDenominator,h.clock.trans g.clock⟩

theorem cachePut_metadata {n : ℕ} (q : ℚ) (Q N j : ℕ) (b : Table n) :
    CacheTableMetadata (cachePut q Q N j b) b := by
  unfold cachePut Table.setD
  split_ifs <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem CacheTableMetadata.widthBound {n : ℕ} {b base : Table n} {W : ℕ}
    (h : CacheTableMetadata b base) (hb : base.MetadataWidth W) : b.MetadataWidth W :=
  ⟨by simpa only [h.width] using hb.width,by simpa only [h.basePositive] using hb.basePositive,
    by simpa only [h.baseNegative] using hb.baseNegative,
    by simpa only [h.baseDenominator] using hb.baseDenominator,by simpa only [h.clock] using hb.clock⟩
theorem CacheTableMetadata.separated {n : ℕ} {b base : Table n}
    (h : CacheTableMetadata b base) (hb : base.Separated) : b.Separated := by
  simpa only [Table.Separated,h.width,h.basePositive,h.baseNegative,h.baseDenominator] using hb
theorem CacheTableMetadata.separatedFrom {n m : ℕ} {a : Table n} {b base : Table m}
    (h : CacheTableMetadata b base) (hb : a.SeparatedFrom base) : a.SeparatedFrom b := by
  simpa only [Table.SeparatedFrom,h.width,h.basePositive,h.baseNegative,h.baseDenominator] using hb

theorem cachePut_real {n : ℕ} (q : ℚ) (Q N j : ℕ) (b : Table n) (hj : 2*j+1<n)
    (hw : (waveCacheReal q Q N j).Width (addressValue b.width)) :
    (cachePut q Q N j b).get ⟨2*j,by omega⟩=waveCacheReal q Q N j := by
  rw [cachePut,Table.setD_get_ne _ (2*j+1) ⟨2*j,by omega⟩ _ (by change 2*j+1≠2*j;omega)]
  simp only [Table.setD,dite_eq_left (by omega : 2*j<n)]
  exact Table.set_get _ _ _ hw
theorem cachePut_imag {n : ℕ} (q : ℚ) (Q N j : ℕ) (b : Table n) (hj : 2*j+1<n)
    (hw : (waveCacheImag q Q N j).Width (addressValue b.width)) :
    (cachePut q Q N j b).get ⟨2*j+1,hj⟩=waveCacheImag q Q N j := by
  simp only [cachePut,Table.setD,dite_eq_left hj,dite_eq_left (by omega : 2*j<n)]
  exact Table.set_get _ _ _ hw
theorem cachePut_other {n : ℕ} (q : ℚ) (Q N j : ℕ) (b : Table n) (k : Fin n)
    (hj0 : 2*j≠k.val) (hj1 : 2*j+1≠k.val) :
    (cachePut q Q N j b).get k=b.get k := by
  rw [cachePut,Table.setD_get_ne _ _ _ _ hj1,Table.setD_get_ne _ _ _ _ hj0]

def CacheContents (q : ℚ) (Q N D remaining : ℕ) (b : Table (2*D)) : Prop :=
  ∀j (hj : j<D),remaining ≤ j →
    b.get ⟨2*j,by omega⟩=waveCacheReal q Q N j ∧
    b.get ⟨2*j+1,by omega⟩=waveCacheImag q Q N j

theorem cacheContents_initial (q : ℚ) (Q N D : ℕ) (b : Table (2*D)) : CacheContents q Q N D D b := by
  intro j hj hr
  omega
theorem cacheContents_put (q : ℚ) (Q N D r : ℕ) (b : Table (2*D)) (hr : r<D)
    (h : CacheContents q Q N D (r+1) b)
    (hw0 : (waveCacheReal q Q N r).Width (addressValue b.width))
    (hw1 : (waveCacheImag q Q N r).Width (addressValue b.width)) :
    CacheContents q Q N D r (cachePut q Q N r b) := by
  intro j hj hrj
  by_cases he : j=r
  · subst j
    exact ⟨cachePut_real q Q N r b (by omega) hw0,cachePut_imag q Q N r b (by omega) hw1⟩
  · have old := h j hj (by omega)
    constructor
    · rw [cachePut_other q Q N r b ⟨2*j,by omega⟩
        (by change 2*r≠2*j;omega) (by change 2*r+1≠2*j;omega)]
      exact old.1
    · rw [cachePut_other q Q N r b ⟨2*j+1,by omega⟩
        (by change 2*r≠2*j+1;omega) (by change 2*r+1≠2*j+1;omega)]
      exact old.2

#print axioms cacheContents_put
end Maxwell.Continuum.Profile.WaveMachine.Runtime
