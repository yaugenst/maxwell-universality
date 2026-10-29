import Maxwell.Cost.CalibrationMatrix.Horner.Store

namespace Maxwell.Cost.CalibrationMatrix.Horner
open Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 1000000

/-- Common machine scratch and the actual zero-valued row/column cursors. -/
def WorkReady (count : List Bool) (B : ℕ) (s : BitRAMState) : Prop :=
  ∃ vi : List Bool, addressValue vi = 0 ∧ vi.length ≤ B ∧ CalibrationMatrix.Ready s (dotValues 0 0) ∧
    Indices s [] vi ∧ BankArray.Word s 104 [] ∧ BankArray.Word s 107 count ∧
    Blank s 106 ∧ Blank s 37 ∧ Blank s 108 ∧ Blank s 109

structure Ports {n : ℕ} (d : Data n) (ip iq op oq : Fin 12) (s : BitRAMState) : Prop where
  inputPositive : BankArray.Word s 112 (d.bases ip)
  inputNegative : BankArray.Word s 113 (d.bases iq)
  outputPositive : BankArray.Word s 114 (d.bases op)
  outputNegative : BankArray.Word s 115 (d.bases oq)

def Data.productData {n : ℕ} (d : Data n) (words : Fin 12 → Vector (List Bool) n) (ip iq : Fin 12) :
    CalibrationMatrix.Data (n*n) n :=
  ⟨d.width, d.clock, d.matrixPositiveBase, d.matrixNegativeBase, d.bases ip, d.bases iq,
    d.matrixPositive, d.matrixNegative, words ip, words iq, d.width_nonempty, d.clock_length⟩

def Data.productBuffers {n : ℕ} (d : Data n) (words : Fin 12 → Vector (List Bool) n)
    (ip iq op oq : Fin 12) : Buffers n :=
  ⟨d.productData words ip iq, ⟨d.bases op,d.bases oq⟩, words op, words oq⟩

def productWords {n : ℕ} (d : Data n) (words : Fin 12 → Vector (List Bool) n) (ip iq op oq : Fin 12) :=
  setOutputs words op oq (Vector.ofFn (d.productData words ip iq).positivePayload)
    (Vector.ofFn (d.productData words ip iq).negativePayload)

theorem productBuffers_sized {n B : ℕ} {d : Data n} (words : Fin 12 → Vector (List Bool) n)
    (ip iq op oq : Fin 12) (h : d.Sized B) : (d.productBuffers words ip iq op oq).Sized B :=
  ⟨⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1 ip,h.2.2.2.2.1 iq⟩,
    h.2.2.2.2.1 op,h.2.2.2.2.1 oq⟩

theorem productBuffers_separated {n : ℕ} (d : Data n) (words : Fin 12 → Vector (List Bool) n)
    (ip iq op oq : Fin 12) (hipiq : ip ≠ iq) (hopoq : op ≠ oq)
    (hipop : ip ≠ op) (hipoq : ip ≠ oq) (hiqop : iq ≠ op) (hiqoq : iq ≠ oq) :
    (d.productBuffers words ip iq op oq).Separated :=
  ⟨⟨d.matrixPositive_separated op,d.matrixPositive_separated oq,
      d.matrixNegative_separated op,d.matrixNegative_separated oq,
      d.separated ip op hipop,d.separated ip oq hipoq,d.separated iq op hiqop,d.separated iq oq hiqoq⟩,
    d.separated op oq hopoq, d.separated ip iq hipiq,
    d.matrixPositive_separated ip,d.matrixPositive_separated iq,
    d.matrixNegative_separated ip,d.matrixNegative_separated iq⟩

theorem productBuffers_ready {n B : ℕ} {d : Data n} {words : Fin 12 → Vector (List Bool) n}
    {count : List Bool} {s : BitRAMState} {ip iq op oq : Fin 12}
    (hw : WorkReady count B s) (hd : Stored d words s) (hp : Ports d ip iq op oq s) :
    (d.productBuffers words ip iq op oq).Ready count B s := by
  obtain ⟨vi, hvi, hvl, hr, hi, h104, h107, h106, h37, h108, h109⟩ := hw
  exact ⟨vi,hvi,hvl,hr,
    ⟨hd.width,hd.clock,hd.matrixPositiveBase,hd.matrixNegativeBase,hp.inputPositive,hp.inputNegative,
      hd.matrixPositive,hd.matrixNegative,hd.arrays ip,hd.arrays iq⟩,hi,
    ⟨h104,hp.outputPositive,hp.outputNegative,hd.arrays op,hd.arrays oq⟩,
    h107,h106,h37,h108,h109⟩

/-- A full finite matrix product between two chosen persistent vector
pairs, with all other twelve-port arrays retained. -/
theorem multiply {n : ℕ} (d : Data n) (words : Fin 12 → Vector (List Bool) n)
    (ip iq op oq : Fin 12) (hipiq : ip ≠ iq) (hopoq : op ≠ oq)
    (hipop : ip ≠ op) (hipoq : ip ≠ oq) (hiqop : iq ≠ op) (hiqoq : iq ≠ oq)
    (B : ℕ) (hsized : d.Sized B) (hm : n*n < 2^B) (hn : n < 2^B)
    (hfit : (d.productBuffers words ip iq op oq).Fits)
    (input : List Bool) (tape : ℕ → Bool) (count : List Bool)
    (hcount : addressValue count = n) (hcl : count.length ≤ B)
    (s : Store) (hw : WorkReady count B s.val) (hd : Stored d words s.val) (hp : Ports d ip iq op oq s.val) :
    ∃ cost, ∃ t : Store, cost ≤ powerStepCost n B ∧ Executes input tape powerStepCode cost s t ∧
      WorkReady count B t.val ∧ Stored d (productWords d words ip iq op oq) t.val ∧
      Ports d op oq ip iq t.val ∧ t.val.tapes 140 = s.val.tapes 140 ∧
      CalibrationMatrix.PowerFrame s.val t.val ∧
      OutputOutside ⟨d.bases op,d.bases oq⟩ n (addressValue d.width) s.val t.val := by
  obtain ⟨cost,t,hcost,he,htr,ht140,htf,htm⟩ := power_step (d.productBuffers words ip iq op oq) B
    (productBuffers_sized words ip iq op oq hsized)
    (productBuffers_separated d words ip iq op oq hipiq hopoq hipop hipoq hiqop hiqoq)
    hfit hm hn d.width_positive input tape count hcount hcl s (productBuffers_ready hw hd hp)
  obtain ⟨vi,hvi,hvl,hr,hdat,hi,hout,h107,h106,h37,h108,h109⟩ := htr
  refine ⟨cost,t,hcost,he,⟨vi,hvi,hvl,hr,hi,hout.index,h107,h106,h37,h108,h109⟩,
    ?_,⟨hdat.vectorPositiveBase,hdat.vectorNegativeBase,hout.positiveBase,hout.negativeBase⟩,ht140,htf,htm⟩
  exact hd.after_output op oq hopoq _ _ htf htm hdat.vectorPositive hdat.vectorNegative

end Maxwell.Cost.CalibrationMatrix.Horner
