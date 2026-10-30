import Maxwell.Continuum.ProfileStartupFrames
import Maxwell.Continuum.ProfileRawWidthPolynomial

/-! The coefficient constructor starts from a stored requested precision;
all transform parameters are computed, then all encoded coefficients are
stored by the actual fixed Boolean program. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
attribute [local irreducible] profileDegree profileWorkBits profileGrid encodedCoefficient

def initializedTableCode : Code := .seq startupCode encodedTableCode
def initializedTableCost (N W B oldLength : ℕ) : ℕ := startupCost N B oldLength+
  encodedTableCost (profileGrid N) (profileDegree N) (profileWorkBits N) (producerSize N) W
    (profileDegree N).bits.length

theorem initialized_table_executes (N W B : ℕ) (hW : 1≤W) (hN : N.bits.length≤B) (hB : 9≤B)
    (a b : PartArray.Table (profileDegree N))
    (ham : a.MetadataWidth W) (hfit : roundedRawWidth (producerSize N)≤addressValue a.width)
    (has : a.Separated) (hdis : b.SeparatedFrom a)
    (hbm : b.MetadataWidth (encodedTableWidth (profileDegree N) W))
    (hslot : encodedTableWidth (profileDegree N) W≤addressValue b.width) (hbs : b.Separated)
    (hbank : roundedWidth (profileGrid N) (producerSize N)≤W)
    (hn : (profileDegree N).bits.length≤W) (hpow : ((2:ℕ)^profileWorkBits N).bits.length≤W)
    (v : ℕ→Parts) (hv : WidthBank dftRegisters (roundedWidth (profileGrid N) (producerSize N)) v)
    (saved : Parts) (hsv : saved.Width (roundedWidth (profileGrid N) (producerSize N)))
    (input : List Bool) (tape : ℕ→Bool) (inner oldWord : List Bool)
    (hlen : inner.length≤roundedWidth (profileGrid N) (producerSize N)) (s : Store)
    (hd : NatAssign.Bank dimensionIds (initialDimensions N) s.val)
    (hz : ∀i∈startupBlanks,Blank s.val i) (hr : Ready dftRegisters v s)
    (hs : StoredParts.Stored 701 saved s.val) (hinner : BankArray.Word s.val 201 inner)
    (hcount : BankArray.Word s.val 700 oldWord)
    (hp : Phase.Runtime.Clean s.val) (hg : Glue.Clean s.val) (hf : DyadicFloor.Clean s.val)
    (ha : a.OutputReady s) (hb : b.Ready s) (hblank : Blank s.val 216) :
    ∃(cost : ℕ) (t : Store) (_result : EncodedTableResult N W b t),
      Executes input tape initializedTableCode cost s t ∧ cost ≤ initializedTableCost N W B oldWord.length := by
  obtain ⟨c0,s0,e0,hc0,params,power,degree,grid,count,z0,f0⟩ :=
    startup_executes N B hN hB input tape oldWord s hd hr.2 hz hcount
  let producer := producerState_after_startup v hr hv saved hs hsv inner hinner hlen hp hg hf z0 f0 params power grid
  obtain ⟨origin,count⟩ := count
  obtain ⟨_,hgrid,hdegree,hwork⟩ := producerSize_bounds N
  obtain ⟨c1,t,result,e1,hc1⟩ := encoded_table_executes N (producerSize N) W hW a b hgrid hdegree hwork
    ham hfit has hdis hbm hslot hbs hbank hn hpow input tape (profileDegree N).bits origin hn
    (addressValue_bits _) s0 producer (startup_output_frame ha z0 f0) (startup_input_frame hb z0 f0)
    degree (blank_of_eq (f0.tapes 216 (by decide)) hblank) count
  exact ⟨c0+c1,t,result,e0.seq e1,by unfold initializedTableCost;omega⟩

#print axioms initialized_table_executes
end Maxwell.Continuum.Profile.Runtime
