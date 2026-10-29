import Maxwell.Cost.CalibrationMatrix.SourceInit.Horner
import Maxwell.Cost.CalibrationMatrix.Horner.PreparePorts
import Maxwell.Cost.CalibrationMatrix.Horner.Semantics

namespace Maxwell.Cost.CalibrationMatrix.SourceInit
open Structured
open RationalAccumulator (Blank)
open scoped BigOperators
set_option maxHeartbeats 1600000

def snapshot {m n : ℕ} (d : Data m n) (h : Horner.Data n)
    (initial : Fin 12 → Vector (List Bool) n) : Horner.Snapshot n :=
  ⟨h,hornerWords initial (outputWords d m)⟩

theorem snapshot_decodes {m n : ℕ} (d : Data m n) (h : Horner.Data n)
    (initial : Fin 12 → Vector (List Bool) n) (A : ChannelMatrix n) (D S : ℕ)
    (hA : h.DecodesMatrix A) (hK : h.K = D^3) (hS : h.S = S)
    (hp : (∑ j, d.records.positive j).bits.length ≤ addressValue d.width)
    (hn : (∑ j, d.records.negative j).bits.length ≤ addressValue d.width) :
    (snapshot d h initial).Decodes A D S (values d.records m,values d.records m) := by
  refine ⟨hA,hK,hS,?_,?_⟩
  · apply congrArg₂ Channels.mk <;> funext i
    · simpa [Horner.channels,snapshot,hornerWords,values] using outputWords_value d m i 0
        (values_positive_bits_le d.records m _ hp i) (values_negative_bits_le d.records m _ hn i)
    · simpa [Horner.channels,snapshot,hornerWords,values] using outputWords_value d m i 1
        (values_positive_bits_le d.records m _ hp i) (values_negative_bits_le d.records m _ hn i)
  · apply congrArg₂ Channels.mk <;> funext i
    · simpa [Horner.channels,snapshot,hornerWords,values] using outputWords_value d m i 2
        (values_positive_bits_le d.records m _ hp i) (values_negative_bits_le d.records m _ hn i)
    · simpa [Horner.channels,snapshot,hornerWords,values] using outputWords_value d m i 3
        (values_positive_bits_le d.records m _ hp i) (values_negative_bits_le d.records m _ hn i)

def readyCode : Code := .seq code Horner.preparePortsCode

def readyCost (m n B : ℕ) : ℕ := costBound m n B+84*B+85

/-- Dense initialization and the actual descriptor copies establish the
kernel's complete entry invariant; neither live source vector is assumed. -/
theorem ready {m n : ℕ} (d : Data m n) (h : Horner.Data n)
    (hwidth : d.width = h.width)
    (hbases : ∀ i : Fin 4, d.outputBases i = h.bases ⟨i.val, by omega⟩)
    (initial : Fin 12 → Vector (List Bool) n)
    (B : ℕ) (hd : d.Sized B) (hh : h.Sized B) (hm : m < 2^B) (hn : n < 2^B)
    (hp : (∑ j, d.records.positive j).bits.length ≤ addressValue d.width)
    (hq : (∑ j, d.records.negative j).bits.length ≤ addressValue d.width)
    (old : Fin 4 → List Bool) (hold : ∀ i, (old i).length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hready : Ready s.val (dotValues 0 0))
    (hdata : Stored d (fun i => initial ⟨i.val,by omega⟩) s.val)
    (hhdata : Horner.Stored h initial s.val)
    (h102 : BankArray.Word s.val 102 []) (h103 : BankArray.Word s.val 103 [])
    (h104 : BankArray.Word s.val 104 []) (h37 : Blank s.val 37)
    (h106 : Blank s.val 106) (h108 : Blank s.val 108) (h109 : Blank s.val 109)
    (hports : ∀ i : Fin 4, BankArray.Word s.val (112+i.val) (old i)) :
    ∃ steps t, steps ≤ readyCost m n B ∧ Executes input tape readyCode steps s t ∧
      (snapshot d h initial).Ready d.dimension B t.val ∧
      PowerFrame s.val t.val ∧ Outside d s.val t.val ∧
      (∀ i, 120 ≤ i → t.val.tapes i = s.val.tapes i) := by
  obtain ⟨sc,a,hsc,ea,ad,ar,a102,a103,a104,a37,a106,a108,af,aout⟩ :=
    executes d (fun i => initial ⟨i.val,by omega⟩) B hd hm hn hp hq input tape s
      hready hdata h102 h103 h104 h37 h106 h108
  have keepA (i : ℕ) (hi : 109 ≤ i) : a.val.tapes i = s.val.tapes i :=
    af.2.2.2.1 i (Or.inr (by omega)) (Or.inr (by omega))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have ah : Horner.Stored h (hornerWords initial (outputWords d m)) a.val :=
    horner_stored d h hwidth hbases initial (outputWords d m) s.val a.val hhdata ad af aout
  have aw : Horner.WorkReady d.dimension B a.val :=
    ⟨[],rfl,by simp,ar,⟨a102,a103⟩,a104,ad.dimension,a106,a37,a108,
      RationalAccumulator.blank_of_eq (keepA 109 (by omega)) h109⟩
  obtain ⟨t,et,hpc,tr,tf⟩ := Horner.prepare_ports h (hornerWords initial (outputWords d m))
    B hh old hold input tape d.dimension a aw ah
    (fun i => BankArray.word_of_eq (keepA _ (by omega)) (hports i))
  have keepT (i : ℕ) (h112 : i ≠ 112) (h113 : i ≠ 113) (h114 : i ≠ 114) (h115 : i ≠ 115) :
      t.val.tapes i = a.val.tapes i :=
    tf.2.2.2.2.2.1 i (by simp [Horner.portAssignments,h112,h113,h114,h115])
  have ptf : PowerFrame a.val t.val :=
    ⟨tf.2.1,tf.2.2.2.1,tf.2.2.2.2.1,
      fun i _ _ _ _ _ _ _ _ _ hi hj hk hl _ => keepT i hi hj hk hl,
      fun i _ h24 h25 h26 h27 _ _ => tf.2.2.2.2.2.2 i h24 h25 h26 h27⟩
  exact ⟨sc+WordAssign.price Horner.portAssignments (Horner.portWords h old),t,
    by dsimp [readyCost]; omega,ea.seq et,tr,(PowerFrame.of_matrix af).trans ptf,
    aout.trans (Outside.of_memory tf.2.2.1),
    fun i hi => (keepT i (by omega) (by omega) (by omega) (by omega)).trans (keepA i (by omega))⟩

end Maxwell.Cost.CalibrationMatrix.SourceInit
