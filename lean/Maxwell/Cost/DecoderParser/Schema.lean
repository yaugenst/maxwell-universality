import Maxwell.Cost.DecoderParser.Lists

namespace Maxwell.Cost.DecoderParser
open Structured

/-- One finite parser is compiled from the static codec schema. -/
def parser : Shape → ℕ → Code
  | .bit, _ => .call (readBit 18)
  | .nat, _ => natural
  | .pair left right, depth => .seq (parser left depth) (parser right depth)
  | .list element, depth => listCode depth (parser element (depth+1))

def price : (shape : Shape) → Payload shape → ℕ
  | .bit, _ => 5
  | .nat, n => 71*n.bits.length+67
  | .pair left right, (x,y) => price left x + price right y
  | .list element, xs => listPrice (price element) xs

theorem parser_correct (shape : Shape) (depth : ℕ) :
    Parses shape (parser shape depth) depth (price shape) := by
  induction shape generalizing depth with
  | bit => exact parses_bit depth
  | nat => exact parses_nat depth
  | pair left right ihl ihr => exact parses_pair left right _ _ depth _ _ (ihl depth) (ihr depth)
  | list element ih => exact parses_list element _ depth _ (ih (depth+1))

abbrev rationalShape : Shape := .pair .bit (.pair .nat .nat)
def rationalPayload (q : ℚ) : Payload rationalShape := (decide (q.num < 0),q.num.natAbs,q.den)

theorem rational_wire (q : ℚ) : wire rationalShape (rationalPayload q) = Codec.rat q := by
  rfl

abbrev edgeShape : Shape := .pair .nat (.pair .nat (.pair .nat .nat))
def edgePayload {B : Target.Box} : B.Edge → Payload edgeShape
  | .inl (i,j,k) => ((0:ℕ),i.val,j.val,k.val)
  | .inr (.inl (i,j,k)) => ((1:ℕ),i.val,j.val,k.val)
  | .inr (.inr (i,j,k)) => ((2:ℕ),i.val,j.val,k.val)

theorem edge_wire {B : Target.Box} (e : B.Edge) : wire edgeShape (edgePayload e) = Codec.edge e := by
  rcases e with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩) <;>
    simp [wire,edgePayload,Codec.edge,List.append_assoc]

abbrev weightShape : Shape := .pair .nat rationalShape
abbrev rowShape : Shape := .pair rationalShape (.list weightShape)
abbrev decoderShape : Shape := .pair .nat (.pair .nat (.pair (.list edgeShape) (.list rowShape)))

def decoderPayload {B : Target.Box} {n : ℕ} (D : Target.WeightedDecoder B.Edge n) :
    Payload decoderShape :=
  (D.format.integerBits,D.format.fractionalBits,
    (List.ofFn D.coordinate).map edgePayload,
    (List.finRange n).map fun i => (rationalPayload (D.offset i),
      ((D.support i).sort).map fun j => (j.val,rationalPayload (D.weight i j))))

theorem list_wire_map {shape : Shape} {α : Type*} (xs : List α) (f : α → Payload shape) :
    wire (.list shape) (xs.map f) = Codec.list (fun x => wire shape (f x)) xs := by
  simp [wire,Codec.list,List.flatMap_map]

theorem decoder_wire {B : Target.Box} {n : ℕ} (D : Target.WeightedDecoder B.Edge n) :
    wire decoderShape (decoderPayload D) = Codec.decoder D := by
  have hrow (i : Fin n) : wire rowShape
      (rationalPayload (D.offset i),
        ((D.support i).sort).map fun j => (j.val,rationalPayload (D.weight i j))) =
      Codec.rat (D.offset i) ++ Codec.list
        (fun j : Fin D.sampleCount => Codec.nat j.val ++ Codec.rat (D.weight i j))
        ((D.support i).sort) := by
    change wire rationalShape _ ++ wire (.list weightShape) _ = _
    rw [rational_wire,list_wire_map]
    rfl
  change Codec.nat D.format.integerBits ++ (Codec.nat D.format.fractionalBits ++
    (wire (.list edgeShape) _ ++ wire (.list rowShape) _)) = _
  rw [list_wire_map,list_wire_map]
  simp only [edge_wire,hrow]
  simp only [Codec.decoder,List.append_assoc]

abbrev targetShape : Shape := .pair .nat (.pair .nat (.pair .nat (.pair .nat
  (.pair (.list rationalShape) (.pair (.list rationalShape) (.pair rationalShape decoderShape))))))

def targetPayload {n : ℕ} (I : Target.Instance n) : Payload targetShape :=
  (n,I.box.nx,I.box.ny,I.box.nz,
    (Codec.cells I.box).map (fun c => rationalPayload (I.material.value c)),
    (Codec.edges I.box).map (fun e => rationalPayload (I.source e)),
    rationalPayload I.tolerance,decoderPayload I.decoder)

theorem target_wire {n : ℕ} (I : Target.Instance n) :
    wire targetShape (targetPayload I) = Codec.target I := by
  change Codec.nat n ++ (Codec.nat I.box.nx ++ (Codec.nat I.box.ny ++ (Codec.nat I.box.nz ++
    (wire (.list rationalShape) _ ++ (wire (.list rationalShape) _ ++
      (wire rationalShape _ ++ wire decoderShape _)))))) = _
  rw [list_wire_map,list_wire_map,rational_wire,decoder_wire]
  simp [rational_wire,Codec.target,List.append_assoc]

/-- Literal code independent of dimensions, material, decoder weights and messages. -/
def targetProgram : BitRAM := (parser targetShape 0).compile

def targetPrice {n : ℕ} (I : Target.Instance n) : ℕ := price targetShape (targetPayload I)

/-- The complete canonical physical target is really parsed. The retained
archive is byte-for-byte its encoding, and the input head is now at the raw
fixed-width access messages. All arithmetic and metadata tapes are untouched. -/
theorem target_run {n : ℕ} (I : Target.Instance n) (w : I.decoder.Messages)
    (randomTape : ℕ → Bool) :
    ∃ (cost : ℕ) (t : Store),
      (runPriced (targetProgram.next (Codec.target I ++ Codec.messages I.decoder w) randomTape)
        (targetPrice I+1) BitRAMState.initial).finished = some (t.place (parser targetShape 0).size) ∧
      (runPriced (targetProgram.next (Codec.target I ++ Codec.messages I.decoder w) randomTape)
        (targetPrice I+1) BitRAMState.initial).instructions = cost ∧ cost ≤ targetPrice I ∧
      t.val.inputHead = (Codec.target I).length ∧
      t.val.tapes 18 = BitTape.atEnd (Codec.target I) ∧
      Frame {18} BitRAMState.initial t.val := by
  obtain ⟨cost,t,ht,hc,hh,hl,hf⟩ := parser_correct targetShape 0 (by decide) (targetPayload I) []
    (Codec.messages I.decoder w) [] randomTape (Store.ofState BitRAMState.initial)
    rfl (by simp [Ready,Store.ofState,BitRAMState.initial])
    (by simp [Store.ofState,BitRAMState.initial,BitTape.atEnd_nil])
  simp only [List.nil_append,target_wire] at ht hh hl
  obtain ⟨hfinish,hcost⟩ := ht.compiled_run (targetPrice I+1) (by dsimp [targetPrice];omega)
  exact ⟨cost,t,hfinish,hcost,hc,by simpa [Store.ofState,BitRAMState.initial] using hh,hl,
    ⟨hf.address,hf.memory,hf.randomCursor,hf.output,hf.tapes⟩⟩

end Maxwell.Cost.DecoderParser
