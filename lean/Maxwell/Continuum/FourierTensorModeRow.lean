import Maxwell.Continuum.FourierTensorModeReset
import Maxwell.Continuum.FourierTensorModeWrite

/-! One complete row of the mode-to-template compiler. Every input read,
rounding operation, indexed output write and scratch reset is charged. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrepare
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def rowCode (j : Fin 3) : Code := .seq (code j) (.seq writeCode resetCode)

theorem row_executes (P R W : ℕ) (hW : 2≤W)
    (a : Table (2*aliasArraySize R)) (b : Table (5*RowArithmetic.rowCount R)) (j : Fin 3)
    (r : Fin (RowArithmetic.rowCount R)) (v : ℕ→Parts)
    (hma : a.MetadataWidth W) (hmb : b.MetadataWidth W)
    (hw : WidthBank RowArithmetic.bank W v) (hg : Good RowArithmetic.bank v)
    (hav : ∀i,(a.get i).Valid) (hR : R.bits.length≤W) (hsize : (aliasArraySize R).bits.length≤W)
    (hfit : ∀x∈writePlan,(values P R a j r v x.2).Width (addressValue b.width))
    (hpos : 0<addressValue b.width) (hsep : b.Separated) (hdisj : a.SeparatedFrom b)
    (input : List Bool) (tape : ℕ→Bool) (word : List Bool) (hlen : word.length≤W)
    (hrow : addressValue word=r.val) (s : Store)
    (hr : RationalDataflow.Ready RowArithmetic.bank v s) (ha : a.Ready s) (hb : b.OutputReady s)
    (hc : BankArray.Word s.val 201 word)
    (hn : NatAssign.Bank ModeIndex.ports (ModeIndex.initial R (aliasArraySize R) 0) s.val)
    (hz : DyadicFloor.Clean s.val) (hp : Word s.val 144 (2^P)) :
    ∃cost t,Executes input tape (rowCode j) cost s t ∧ cost≤2^210*(P+W+11)^2 ∧
      RationalDataflow.Ready RowArithmetic.bank (canonical v) t ∧
      WidthBank RowArithmetic.bank W (canonical v) ∧ Good RowArithmetic.bank (canonical v) ∧
      a.Ready t ∧ (written P R a b j r v).OutputReady t ∧
      NatAssign.Bank ModeIndex.ports (ModeIndex.initial R (aliasArraySize R) 0) t.val ∧
      DyadicFloor.Clean t.val ∧ Word t.val 144 (2^P) ∧ BankArray.Word t.val 201 word ∧
      t.val.tapes 201=s.val.tapes 201 ∧ t.val.output=s.val.output := by
  obtain ⟨c0,s0,e0,hc0,r0,w0,g0,a0,b0,n0,wn0,z0,p0,i0,f0,o0⟩ := executes P R W hW a b j r v
    hma hw hg hav hR hsize input tape word hlen hrow s hr ha hb hc hn hz hp
  obtain ⟨c1,s1,e1,hc1,r1,a1,b1,n1,z1,p1,i1,f1,o1⟩ := write_executes P R W a b j r v hmb hfit hpos hsep hdisj
    input tape word hlen hrow s0 r0 a0 b0 i0 n0 z0 p0
  obtain ⟨c2,t,e2,hc2,r2,a2,b2,n2,z2,p2,i2,f2,o2⟩ := reset_executes P R (2^15*(P+W+1)) (128*(W+1)+8)
    (by omega) a (written P R a b j r v) j r v w0 g0 wn0 input tape word s1 r1 a1 b1 n1 z1 p1 i1
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,r2,canonical_width v W (by omega) hw,
    canonical_good v hg,a2,b2,n2,z2,p2,i2,f2.trans (f1.trans f0),o2.trans (o1.trans o0)⟩
  nlinarith only [hc0,hc1,hc2,Nat.zero_le P,Nat.zero_le W]

#print axioms row_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrepare
