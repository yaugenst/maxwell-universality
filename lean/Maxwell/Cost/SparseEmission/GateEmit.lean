import Maxwell.Cost.SparseEmission.Entry

namespace Maxwell.Cost.SparseEmission.GateEmit
open Structured
open SourceCircuit (Frame)

def diagonal (row : List Bool) : List Bool := row++row++[false,false]
def offDiagonal (row parent : List Bool) (negative half : Bool) : List Bool := row++parent++[negative,half]

structure Context (row clock : List Bool) (rowOrigin clockOrigin : ℤ) (s : Store) : Prop where
  rowWord : s.val.tapes 113 = BitTape.shifted row rowOrigin
  clockWord : s.val.tapes 93 = BitTape.shifted clock clockOrigin
  temporary : s.val.tapes 114 = BitTape.blank

def work : Finset ℕ := {110,111,112,114}
def unaryWork : Finset ℕ := {110,111,114}

def zeroCode : Code := .seq (CopyEnd.code 113 111) (Entry.code 111 false false)
def scaleCode (negative half : Bool) : Code := .seq (Entry.code 111 negative half) zeroCode
def addCode : Code := .seq (Entry.code 112 true false) (scaleCode true false)

theorem zero_executes (input : List Bool) (randomTape : ℕ → Bool)
    (row clock preceding : List Bool) (origin rowOrigin clockOrigin : ℤ) (s : Store)
    (hlen : clock.length = row.length) (hctx : Context row clock rowOrigin clockOrigin s)
    (ha : s.val.tapes 110 = BitTape.shifted preceding origin)
    (h111 : s.val.tapes 111 = BitTape.blank) :
    ∃ t, Executes input randomTape zeroCode (70*row.length+75) s t ∧
      t.val.tapes 110 = BitTape.shifted (diagonal row++preceding) (origin-(2*row.length+2)) ∧
      t.val.tapes 111 = BitTape.blank ∧ Context row clock rowOrigin clockOrigin t ∧
      t.val.address = s.val.address ∧ t.val.memory = s.val.memory ∧
      Frame unaryWork s.val t.val ∧ (∀ i, i ∉ unaryWork → t.val.tapes i = s.val.tapes i) := by
  obtain ⟨a,ea,a111,aa,am,af,ak⟩ := CopyEnd.executes 113 111 (by decide) input randomTape
    row rowOrigin s hctx.rowWord h111
  obtain ⟨t,et,ta,t111,t114,taAddress,tm,tf,tk⟩ := Entry.executes 111 (Or.inl rfl) false false
    input randomTape row row clock preceding origin rowOrigin clockOrigin a rfl hlen
      ((ak 110 (by decide)).trans ha) ((ak 113 (by decide)).trans hctx.rowWord) a111
      ((ak 93 (by decide)).trans hctx.clockWord) ((ak 114 (by decide)).trans hctx.temporary)
  have keep (i : ℕ) (hi : i ∉ unaryWork) : t.val.tapes i = s.val.tapes i := by
    have hit : i ∉ Entry.work 111 := by simp_all [unaryWork,Entry.work]
    have hi111 : i ≠ 111 := by simp_all [unaryWork]
    exact (tk i hit).trans (ak i hi111)
  refine ⟨t,?_,ta,t111,⟨(keep 113 (by decide)).trans hctx.rowWord,
    (keep 93 (by decide)).trans hctx.clockWord,t114⟩,
    taAddress.trans aa,tm.trans am,(af.mono (by decide)).trans (tf.mono (by decide)),keep⟩
  convert ea.seq et using 1 <;> first | rfl | omega

theorem scale_executes (negative half : Bool) (input : List Bool) (randomTape : ℕ → Bool)
    (row parent clock preceding : List Bool) (origin rowOrigin clockOrigin : ℤ) (s : Store)
    (hpLen : parent.length = row.length) (hcLen : clock.length = row.length)
    (hctx : Context row clock rowOrigin clockOrigin s)
    (ha : s.val.tapes 110 = BitTape.shifted preceding origin)
    (hp : s.val.tapes 111 = BitTape.atEnd parent) :
    ∃ t, Executes input randomTape (scaleCode negative half) (120*row.length+129) s t ∧
      t.val.tapes 110 = BitTape.shifted (diagonal row++offDiagonal row parent negative half++preceding)
        (origin-2*(2*row.length+2)) ∧
      t.val.tapes 111 = BitTape.blank ∧ Context row clock rowOrigin clockOrigin t ∧
      t.val.address = s.val.address ∧ t.val.memory = s.val.memory ∧
      Frame unaryWork s.val t.val ∧ (∀ i, i ∉ unaryWork → t.val.tapes i = s.val.tapes i) := by
  obtain ⟨a,ea,aa,a111,a114,aaAddress,am,af,ak⟩ := Entry.executes 111 (Or.inl rfl)
    negative half input randomTape row parent clock preceding origin rowOrigin clockOrigin s hpLen hcLen
    ha hctx.rowWord hp hctx.clockWord hctx.temporary
  have actx : Context row clock rowOrigin clockOrigin a :=
    ⟨(ak 113 (by decide)).trans hctx.rowWord,(ak 93 (by decide)).trans hctx.clockWord,a114⟩
  obtain ⟨t,et,ta,t111,tctx,taAddress,tm,tf,tk⟩ := zero_executes input randomTape row clock
    (offDiagonal row parent negative half++preceding) (origin-(2*row.length+2)) rowOrigin clockOrigin
    a hcLen actx aa a111
  refine ⟨t,?_,?_,t111,tctx,taAddress.trans aaAddress,tm.trans am,
    (af.mono (by decide)).trans tf,?_⟩
  · convert ea.seq et using 1 <;> first | rfl | omega
  · simpa [List.append_assoc,sub_sub,two_mul] using ta
  · intro i hi
    exact (tk i hi).trans (ak i (by simp_all [unaryWork,Entry.work]))

theorem add_executes (input : List Bool) (randomTape : ℕ → Bool)
    (row left right clock preceding : List Bool) (origin rowOrigin clockOrigin : ℤ) (s : Store)
    (hlLen : left.length = row.length) (hrLen : right.length = row.length)
    (hcLen : clock.length = row.length) (hctx : Context row clock rowOrigin clockOrigin s)
    (ha : s.val.tapes 110 = BitTape.shifted preceding origin)
    (hl : s.val.tapes 111 = BitTape.atEnd left) (hr : s.val.tapes 112 = BitTape.atEnd right) :
    ∃ t, Executes input randomTape addCode (170*row.length+183) s t ∧
      t.val.tapes 110 = BitTape.shifted
        (diagonal row++offDiagonal row left true false++offDiagonal row right true false++preceding)
        (origin-3*(2*row.length+2)) ∧
      t.val.tapes 111 = BitTape.blank ∧ t.val.tapes 112 = BitTape.blank ∧
      Context row clock rowOrigin clockOrigin t ∧
      t.val.address = s.val.address ∧ t.val.memory = s.val.memory ∧
      Frame work s.val t.val ∧ (∀ i, i ∉ work → t.val.tapes i = s.val.tapes i) := by
  obtain ⟨a,ea,aa,a112,a114,aaAddress,am,af,ak⟩ := Entry.executes 112 (Or.inr rfl) true false
    input randomTape row right clock preceding origin rowOrigin clockOrigin s hrLen hcLen
    ha hctx.rowWord hr hctx.clockWord hctx.temporary
  have actx : Context row clock rowOrigin clockOrigin a :=
    ⟨(ak 113 (by decide)).trans hctx.rowWord,(ak 93 (by decide)).trans hctx.clockWord,a114⟩
  obtain ⟨t,et,ta,t111,tctx,taAddress,tm,tf,tk⟩ := scale_executes true false input randomTape
    row left clock (offDiagonal row right true false++preceding) (origin-(2*row.length+2))
    rowOrigin clockOrigin a hlLen hcLen actx aa ((ak 111 (by decide)).trans hl)
  have t112 : t.val.tapes 112 = BitTape.blank := by
    exact (tk 112 (by decide)).trans a112
  refine ⟨t,?_,?_,t111,t112,tctx,taAddress.trans aaAddress,tm.trans am,
    (af.mono (by decide)).trans (tf.mono (by decide)),?_⟩
  · convert ea.seq et using 1 <;> first | rfl | omega
  · have ho : origin-(2*(row.length:ℤ)+2)-2*(2*row.length+2) = origin-3*(2*row.length+2) := by ring
    simpa [List.append_assoc,Nat.cast_add,Nat.cast_mul,ho] using ta
  · intro i hi
    exact (tk i (by simp_all [work,unaryWork])).trans (ak i (by simp_all [work,Entry.work]))

end Maxwell.Cost.SparseEmission.GateEmit
