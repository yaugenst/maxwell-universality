import Maxwell.Cost.CalibrationMatrix.Horner.DenominatorReady
import Maxwell.Cost.CalibrationMatrix.Pairing

namespace Maxwell.Cost.CalibrationMatrix.Horner
open Structured
open RationalAccumulator (Blank Word)
set_option maxHeartbeats 1500000

structure PairingRow (n : ℕ) where
  positiveBase : List Bool
  negativeBase : List Bool
  positive : Vector (List Bool) n
  negative : Vector (List Bool) n

structure PairingRow.Stored {n : ℕ} (r : PairingRow n) (width : ℕ) (s : BitRAMState) : Prop where
  positiveBase : BankArray.Word s 154 r.positiveBase
  negativeBase : BankArray.Word s 155 r.negativeBase
  positive : BitArray.Represents s.memory (addressValue r.positiveBase) width r.positive
  negative : BitArray.Represents s.memory (addressValue r.negativeBase) width r.negative

def PairingRow.channels {n : ℕ} (r : PairingRow n) : Channels n :=
  ⟨fun i => addressValue (r.positive.get i),fun i => addressValue (r.negative.get i)⟩

def pairingData {n : ℕ} (r : PairingRow n) (d : Scale.Data n) (words : Fin 4 → Vector (List Bool) n) :
    CalibrationMatrix.Data n n :=
  ⟨d.width,d.clock,r.positiveBase,r.negativeBase,d.bases 2,d.bases 3,r.positive,r.negative,
    words 2,words 3,d.width_nonempty,d.clock_length⟩

theorem pairingData_decodes {n : ℕ} (r : PairingRow n) (d : Scale.Data n)
    (words : Fin 4 → Vector (List Bool) n) :
    Pairing.Decodes (pairingData r d words) r.channels (Scale.channels words 2 3) :=
  ⟨fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

structure PairingOld where
  mp : List Bool
  mn : List Bool
  vp : List Bool
  vn : List Bool

def PairingOld.Stored (old : PairingOld) (s : BitRAMState) : Prop :=
  BankArray.Word s 110 old.mp ∧ BankArray.Word s 111 old.mn ∧
  BankArray.Word s 112 old.vp ∧ BankArray.Word s 113 old.vn

def pairingSetupCode : Code := .seq (Assign.code 154 110) (.seq (Assign.code 155 111)
  (.seq (Assign.code 128 112) (.seq (Assign.code 129 113) (.call (WordTransfer.clone 107 106)))))

def pairingSetupCost {n : ℕ} (r : PairingRow n) (d : Scale.Data n) (old : PairingOld) (count : List Bool) : ℕ :=
  6*old.mp.length+4+(15*r.positiveBase.length+17)+
    (6*old.mn.length+4+(15*r.negativeBase.length+17)+
      (6*old.vp.length+4+(15*(d.bases 2).length+17)+
        (6*old.vn.length+4+(15*(d.bases 3).length+17)+(15*count.length+17))))

def PairingSetupFrame (s t : BitRAMState) : Prop :=
  t.memory = s.memory ∧ t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i ≠ 106 → i ≠ 110 → i ≠ 111 → i ≠ 112 → i ≠ 113 → t.tapes i = s.tapes i)

/-- Physical descriptor replacement and a charged count clone put the final
inverse arrays and an independent source row into the exact scalar emitter. -/
theorem pairing_setup {n : ℕ} (r : PairingRow n) (d : Scale.Data n)
    (words : Fin 4 → Vector (List Bool) n) (old : PairingOld) (count : List Bool)
    (B : ℕ) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hw : WorkReady count B s.val) (hd : Scale.Stored d words s.val)
    (hr : r.Stored (addressValue d.width) s.val) (ho : old.Stored s.val) :
    ∃ t : Store, ∃ vi : List Bool, ∃ origin : ℤ,
      Executes input tape pairingSetupCode (pairingSetupCost r d old count) s t ∧
      CalibrationMatrix.Ready t.val (dotValues 0 0) ∧ CalibrationMatrix.Stored (pairingData r d words) t.val ∧
      Indices t.val [] vi ∧ addressValue vi = 0 ∧ vi.length ≤ B ∧
      t.val.tapes 106 = BitTape.shifted count origin ∧ PairingSetupFrame s.val t.val := by
  obtain ⟨a,ea,ha,ka,fa⟩ := Assign.executes 154 110 (by omega) input tape r.positiveBase old.mp s hr.positiveBase ho.1
  obtain ⟨b,eb,hb,kb,fb⟩ := Assign.executes 155 111 (by omega) input tape r.negativeBase old.mn a
    (BankArray.word_of_eq (ka 155 (by omega)) hr.negativeBase)
    (BankArray.word_of_eq (ka 111 (by omega)) ho.2.1)
  obtain ⟨c,ec,hc,kc,fc⟩ := Assign.executes 128 112 (by omega) input tape (d.bases 2) old.vp b
    (BankArray.word_of_eq ((kb 128 (by omega)).trans (ka 128 (by omega))) (hd.bases 2))
    (BankArray.word_of_eq ((kb 112 (by omega)).trans (ka 112 (by omega))) ho.2.2.1)
  obtain ⟨e,ee,he,ke,fe⟩ := Assign.executes 129 113 (by omega) input tape (d.bases 3) old.vn c
    (BankArray.word_of_eq ((kc 129 (by omega)).trans ((kb 129 (by omega)).trans (ka 129 (by omega)))) (hd.bases 3))
    (BankArray.word_of_eq ((kc 113 (by omega)).trans ((kb 113 (by omega)).trans (ka 113 (by omega)))) ho.2.2.2)
  have keepE (i : ℕ) (h110 : i ≠ 110) (h111 : i ≠ 111) (h112 : i ≠ 112) (h113 : i ≠ 113) :
      e.val.tapes i = s.val.tapes i := (ke i h113).trans ((kc i h112).trans ((kb i h111).trans (ka i h110)))
  obtain ⟨vi,hvi,hvl,hready,hidx,h104,h107,h106,h37,h108,h109⟩ := hw
  obtain ⟨co,h107⟩ := h107
  obtain ⟨origin,h106⟩ := h106
  obtain ⟨t,et,ht,ft⟩ := WordCall.clone 107 106 (by omega) input tape count co origin e
    ((keepE 107 (by omega) (by omega) (by omega) (by omega)).trans h107)
    ((keepE 106 (by omega) (by omega) (by omega) (by omega)).trans h106)
  have keepT (i : ℕ) (hi : i ≠ 106) : t.val.tapes i = e.val.tapes i := by simp [ht,hi]
  have keep (i : ℕ) (h106 : i ≠ 106) (h110 : i ≠ 110) (h111 : i ≠ 111) (h112 : i ≠ 112) (h113 : i ≠ 113) :
      t.val.tapes i = s.val.tapes i := (keepT i h106).trans (keepE i h110 h111 h112 h113)
  have hm : t.val.memory = s.val.memory := ft.2.2.1.trans (fe.2.2.1.trans (fc.2.2.1.trans (fb.2.2.1.trans fa.2.2.1)))
  refine ⟨t,vi,origin,ea.seq (eb.seq (ec.seq (ee.seq et))),
    hready.of_tapes (fun i hi => keep i (by omega) (by omega) (by omega) (by omega) (by omega)),
    ⟨BankArray.word_of_eq (keep 100 (by omega) (by omega) (by omega) (by omega) (by omega)) hd.width,
      BankArray.word_of_eq (keep 101 (by omega) (by omega) (by omega) (by omega) (by omega)) hd.clock,
      BankArray.word_of_eq ((keepT 110 (by omega)).trans ((ke 110 (by omega)).trans ((kc 110 (by omega)).trans (kb 110 (by omega))))) ha,
      BankArray.word_of_eq ((keepT 111 (by omega)).trans ((ke 111 (by omega)).trans (kc 111 (by omega)))) hb,
      BankArray.word_of_eq ((keepT 112 (by omega)).trans (ke 112 (by omega))) hc,
      BankArray.word_of_eq (keepT 113 (by omega)) he,
      by simpa only [hm,pairingData] using hr.positive,by simpa only [hm,pairingData] using hr.negative,
      by simpa only [hm,pairingData] using hd.arrays 2,by simpa only [hm,pairingData] using hd.arrays 3⟩,
    ⟨BankArray.word_of_eq (keep 102 (by omega) (by omega) (by omega) (by omega) (by omega)) hidx.1,
      BankArray.word_of_eq (keep 103 (by omega) (by omega) (by omega) (by omega) (by omega)) hidx.2⟩,
    hvi,hvl,by simp [ht],hm,
    ft.2.1.trans (fe.2.1.trans (fc.2.1.trans (fb.2.1.trans fa.2.1))),
    ft.2.2.2.1.trans (fe.2.2.2.1.trans (fc.2.2.2.1.trans (fb.2.2.2.1.trans fa.2.2.2.1))),
    ft.2.2.2.2.1.trans (fe.2.2.2.2.1.trans (fc.2.2.2.2.1.trans (fb.2.2.2.2.1.trans fa.2.2.2.2.1))),keep⟩

theorem pairingSetupCost_le {n : ℕ} (r : PairingRow n) (d : Scale.Data n) (old : PairingOld)
    (count : List Bool) (B : ℕ) (hd : d.Sized B)
    (hp : r.positiveBase.length ≤ B) (hn : r.negativeBase.length ≤ B)
    (hmp : old.mp.length ≤ B) (hmn : old.mn.length ≤ B)
    (hvp : old.vp.length ≤ B) (hvn : old.vn.length ≤ B) (hc : count.length ≤ B) :
    pairingSetupCost r d old count ≤ 100*B+110 := by
  have hp2 := hd.2.2.1 2
  have hn3 := hd.2.2.1 3
  dsimp [pairingSetupCost]
  omega

end Maxwell.Cost.CalibrationMatrix.Horner
