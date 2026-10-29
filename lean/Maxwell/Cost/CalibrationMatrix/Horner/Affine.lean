import Maxwell.Cost.CalibrationMatrix.Horner.Select
import Maxwell.Cost.CalibrationMatrix.Affine.Semantics

namespace Maxwell.Cost.CalibrationMatrix.Horner
open Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 1500000

def affinePort (i : Fin 10) : Fin 12 := ⟨i.val, by omega⟩

def Data.affineData {n : ℕ} (d : Data n) : Affine.Data n where
  width := d.width
  clock := d.clock
  bases := fun i => d.bases (affinePort i)
  K := d.K
  S := d.S
  width_nonempty := d.width_nonempty
  width_positive := d.width_positive
  clock_length := d.clock_length
  separated := fun i j h => d.separated _ _ (by intro he; apply h; apply Fin.ext; exact congrArg (fun k : Fin 12 => k.val) he)

def affineWords {n : ℕ} (words : Fin 12 → Vector (List Bool) n) : Fin 10 → Vector (List Bool) n :=
  fun i => words (affinePort i)

def affineFinalWords {n : ℕ} (d : Data n) (words : Fin 12 → Vector (List Bool) n) :
    Fin 12 → Vector (List Bool) n := fun i =>
  if h : i.val < 10 then Affine.filledWords d.affineData (affineWords words) n ⟨i.val,h⟩ else words i

theorem Data.affine_sized {n B : ℕ} {d : Data n} (h : d.Sized B) : d.affineData.Sized B :=
  ⟨h.1,h.2.1,fun i => h.2.2.2.2.1 (affinePort i),h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩

theorem Stored.to_affine {n : ℕ} {d : Data n} {words : Fin 12 → Vector (List Bool) n}
    {s : BitRAMState} (h : Stored d words s)
    (h114 : BankArray.Word s 114 (d.bases 8)) (h115 : BankArray.Word s 115 (d.bases 9)) :
    Affine.Stored d.affineData (affineWords words) s := by
  refine ⟨h.width,h.clock,?_,h.K,h.S,fun i => h.arrays (affinePort i)⟩
  intro i
  fin_cases i
  · exact h.bases 0
  · exact h.bases 1
  · exact h.bases 2
  · exact h.bases 3
  · exact h.bases 4
  · exact h.bases 5
  · exact h.bases 6
  · exact h.bases 7
  · exact h114
  · exact h115

theorem represents_of_affine {m n width base : ℕ} {values : Vector (List Bool) m}
    {d : Affine.Data n} {s t : BitRAMState} (hw : addressValue d.width = width)
    (h : BitArray.Represents s.memory base width values) (hm : Affine.Outside d s t)
    (hsep : ∀ i, 6 ≤ i.val → IncidenceEncoding.Separated base (m*width)
      (addressValue (d.bases i)) (n*width)) : BitArray.Represents t.memory base width values := by
  refine ⟨h.length,?_⟩
  intro i j hj
  rw [hm]
  · exact h.bits i j hj
  · intro p hp
    rw [hw]
    have hs := Nat.mul_le_mul_right width (show i.val+1 ≤ m by omega)
    rcases hsep p hp with hsep | hsep
    · left; nlinarith
    · right; omega

theorem Stored.after_affine {n : ℕ} {d : Data n} {words : Fin 12 → Vector (List Bool) n}
    {s t : BitRAMState} (h : Stored d words s)
    (ha : Affine.Stored d.affineData (Affine.filledWords d.affineData (affineWords words) n) t)
    (hf : MatrixFrame s t) (hm : Affine.Outside d.affineData s t) :
    Stored d (affineFinalWords d words) t := by
  have keep := PowerFrame.metadata (CalibrationMatrix.PowerFrame.of_matrix hf)
  refine ⟨BankArray.word_of_eq (keep 100 (by simp [Metadata])) h.width,
    BankArray.word_of_eq (keep 101 (by simp [Metadata])) h.clock,
    BankArray.word_of_eq (keep 110 (by simp [Metadata])) h.matrixPositiveBase,
    BankArray.word_of_eq (keep 111 (by simp [Metadata])) h.matrixNegativeBase,
    fun i => BankArray.word_of_eq (keep _ (by right;right;right;right;exact baseBank_bounds i)) (h.bases i),
    RationalAccumulator.word_of_eq (keep 126 (by simp [Metadata])) h.K,
    RationalAccumulator.word_of_eq (keep 127 (by simp [Metadata])) h.S,
    represents_of_affine rfl h.matrixPositive hm (fun i _ => d.matrixPositive_separated (affinePort i)),
    represents_of_affine rfl h.matrixNegative hm (fun i _ => d.matrixNegative_separated (affinePort i)),?_⟩
  intro i
  by_cases hi : i.val < 10
  · have he : affinePort (⟨i.val,hi⟩ : Fin 10) = i := by apply Fin.ext; rfl
    simpa only [affineFinalWords, dite_eq_left hi, Data.affineData,he] using ha.arrays ⟨i.val,hi⟩
  · simp only [affineFinalWords,dite_eq_right hi]
    exact represents_of_affine rfl (h.arrays i) hm (fun p _ =>
      d.separated i (affinePort p) (by intro he; have he' := congrArg Fin.val he; dsimp [affinePort] at he'; omega))

def affineCode : Code := .seq (.call (WordTransfer.clone 107 108))
  (.seq Affine.code (.call (TapeOps.clear 104)))

def affineCost (n B : ℕ) : ℕ := Affine.costBound n B+21*B+21

theorem affine_pass {n : ℕ} (d : Data n) (words : Fin 12 → Vector (List Bool) n)
    (B : ℕ) (hsized : d.Sized B) (hn : n < 2^B)
    (hwp : ∀ i, (Affine.newWPositive d.affineData (affineWords words) i).bits.length ≤ addressValue d.width)
    (hwn : ∀ i, (Affine.newWNegative d.affineData (affineWords words) i).bits.length ≤ addressValue d.width)
    (hxp : ∀ i, (Affine.newXPositive d.affineData (affineWords words) i).bits.length ≤ addressValue d.width)
    (hxn : ∀ i, (Affine.newXNegative d.affineData (affineWords words) i).bits.length ≤ addressValue d.width)
    (input : List Bool) (tape : ℕ → Bool) (count : List Bool)
    (hcount : addressValue count = n) (hcl : count.length ≤ B) (s : Store)
    (hw : WorkReady count B s.val) (hd : Stored d words s.val) (hp : Ports d 4 5 8 9 s.val) :
    ∃ cost, ∃ t : Store, cost ≤ affineCost n B ∧ Executes input tape affineCode cost s t ∧
      WorkReady count B t.val ∧ Stored d (affineFinalWords d words) t.val ∧ Ports d 4 5 8 9 t.val ∧
      t.val.tapes 140 = s.val.tapes 140 ∧ CalibrationMatrix.PowerFrame s.val t.val ∧
      Affine.Outside d.affineData s.val t.val := by
  obtain ⟨vi,hvi,hvl,hr,hi,h104,h107,h106,h37,h108,h109⟩ := hw
  obtain ⟨co,h107⟩ := h107
  obtain ⟨oo,h108⟩ := h108
  obtain ⟨a,ea,ha,fa⟩ := WordCall.clone 107 108 (by omega) input tape count co oo s h107 h108
  have keepA (i : ℕ) (hi : i ≠ 108) : a.val.tapes i = s.val.tapes i := by simp [ha,hi]
  have had := hd.of_memory_tapes fa.2.2.1 (fun i hi => keepA i (by dsimp [Metadata] at hi;omega))
  have frameA : MatrixFrame s.val a.val :=
    ⟨fa.2.1,fa.2.2.2.1,fa.2.2.2.2.1,fun i _ _ _ _ _ _ _ hi => keepA i hi,
      fun i _ h24 h25 h26 h27 _ _ => fa.2.2.2.2.2.2 i h24 h25 h26 h27⟩
  obtain ⟨steps,q,fi,hsteps,eq,hfi,hfil,hqi,hqd,hqr,hq37,hq108,hqcontrol,fq,hqm⟩ :=
    Affine.executes d.affineData (affineWords words) B (Data.affine_sized hsized) hn hwp hwn hxp hxn
      input tape [] count rfl hcount (by simp) hcl oo a
      (hr.of_tapes (fun i hi => keepA i (by omega)))
      (had.to_affine (BankArray.word_of_eq (keepA 114 (by omega)) hp.outputPositive)
        (BankArray.word_of_eq (keepA 115 (by omega)) hp.outputNegative))
      (BankArray.word_of_eq (keepA 104 (by omega)) h104)
      (RationalAccumulator.blank_of_eq (keepA 37 (by omega)) h37) (by simp [ha])
  have hqd' := had.after_affine hqd fq hqm
  obtain ⟨fo,hqi⟩ := hqi
  obtain ⟨t,et,ht,ft⟩ := WordCall.clear 104 input tape fi fo q hqi
  have keepT (i : ℕ) (hi : i ≠ 104) : t.val.tapes i = q.val.tapes i := by simp [ht,hi]
  have frameT : MatrixFrame q.val t.val :=
    ⟨ft.2.1,ft.2.2.2.1,ft.2.2.2.2.1,fun i _ _ _ _ _ hi _ _ => keepT i hi,
      fun i _ _ _ h26 h27 _ _ => ft.2.2.2.2.2.2 i h26 h27⟩
  have keepQ (i : ℕ) (hi : i = 107 ∨ i = 109 ∨ 110 ≤ i) : q.val.tapes i = a.val.tapes i :=
    fq.2.2.2.1 i (Or.inr (by omega)) (Or.inr (by omega)) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  have kept (i : ℕ) (hi : i = 107 ∨ i = 109 ∨ 110 ≤ i) : t.val.tapes i = s.val.tapes i :=
    (keepT i (by omega)).trans ((keepQ i hi).trans (keepA i (by omega)))
  refine ⟨15*count.length+17+(steps+(6*fi.length+4)),t,?_,ea.seq (eq.seq et),?_,
    hqd'.of_memory_tapes ft.2.2.1 (fun i hi => keepT i (by dsimp [Metadata] at hi;omega)),
    ⟨BankArray.word_of_eq (kept 112 (by omega)) hp.inputPositive,
      BankArray.word_of_eq (kept 113 (by omega)) hp.inputNegative,
      BankArray.word_of_eq (kept 114 (by omega)) hp.outputPositive,
      BankArray.word_of_eq (kept 115 (by omega)) hp.outputNegative⟩,
    kept 140 (by omega), CalibrationMatrix.PowerFrame.of_matrix ((frameA.trans fq).trans frameT),
    (Affine.Outside.of_memory fa.2.2.1).trans (hqm.trans (Affine.Outside.of_memory ft.2.2.1))⟩
  · dsimp [affineCost];omega
  · refine ⟨vi,hvi,hvl,hqr.of_tapes (fun i hi => keepT i (by omega)),
      ⟨BankArray.word_of_eq ((keepT 102 (by omega)).trans ((hqcontrol 102 (by omega)).trans (keepA 102 (by omega)))) hi.1,
        BankArray.word_of_eq ((keepT 103 (by omega)).trans ((hqcontrol 103 (by omega)).trans (keepA 103 (by omega)))) hi.2⟩,
      ⟨fo+fi.length,by simp [ht,BitTape.shifted,BitTape.blank]⟩,
      ⟨co,(kept 107 (by omega)).trans h107⟩,
      RationalAccumulator.blank_of_eq ((keepT 106 (by omega)).trans ((hqcontrol 106 (by omega)).trans (keepA 106 (by omega)))) h106,
      RationalAccumulator.blank_of_eq (keepT 37 (by omega)) hq37,
      RationalAccumulator.blank_of_eq (keepT 108 (by omega)) hq108,
      RationalAccumulator.blank_of_eq (kept 109 (by omega)) h109⟩

end Maxwell.Cost.CalibrationMatrix.Horner
