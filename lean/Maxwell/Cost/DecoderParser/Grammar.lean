import Maxwell.Cost.DecoderParser.Primitives
import Maxwell.Cost.Structured.Correctness

namespace Maxwell.Cost.DecoderParser
open Structured

/-- Only the archive remains changed between grammar elements. All parser
scratch tapes are physically restored, while persistent metadata is preserved. -/
def Ready (depth : ℕ) (s : BitRAMState) : Prop :=
  s.tapes 10 = BitTape.blank ∧ s.tapes 11 = BitTape.blank ∧
    s.tapes 45 = BitTape.blank ∧ ∀ i, 46 + depth ≤ i → i < 60 → s.tapes i = BitTape.blank

theorem Ready.frame {depth : ℕ} {s t : BitRAMState} (h : Ready depth s)
    (hf : Frame {18} s t) : Ready depth t := by
  refine ⟨(hf.tapes 10 (by simp)).trans h.1,
    (hf.tapes 11 (by simp)).trans h.2.1,
    (hf.tapes 45 (by simp)).trans h.2.2.1, ?_⟩
  intro i hi h60
  exact (hf.tapes i (by simp; omega)).trans (h.2.2.2 i hi h60)

def natural : Code := .seq (readNat 45 18) (clearWord 45)

theorem natural_steps (depth n : ℕ) (preceding suffix saved : List Bool)
    (randomTape : ℕ → Bool) (s : Store)
    (hhead : s.val.inputHead = preceding.length) (hready : Ready depth s.val)
    (hlog : s.val.tapes 18 = BitTape.atEnd saved) :
    ∃ t : Store,
      Executes (preceding ++ (Codec.nat n ++ suffix)) randomTape natural
        (71 * n.bits.length + 67) s t ∧
      t.val.inputHead = s.val.inputHead + (Codec.nat n).length ∧
      t.val.tapes 18 = BitTape.atEnd (saved ++ Codec.nat n) ∧ Frame {18} s.val t.val := by
  obtain ⟨u, hu, hh, hw, hl, h10, h11, hf⟩ :=
    readNat_steps 45 18 (by decide) (by decide) (by decide) (by decide) (by decide)
      n preceding suffix saved randomTape s hhead hready.1 hready.2.2.1 hready.2.1 hlog
  obtain ⟨t, ht, ht45, hthead, htf⟩ :=
    clearWord_steps 45 (preceding ++ (Codec.nat n ++ suffix)) randomTape n.bits u hw
  refine ⟨t, ?_, hthead.trans hh, (htf.tapes 18 (by simp)).trans hl, ?_⟩
  · convert hu.seq ht using 1 <;> first | rfl | omega
  · refine ⟨htf.address.trans hf.address, htf.memory.trans hf.memory,
      htf.randomCursor.trans hf.randomCursor, htf.output.trans hf.output, ?_⟩
    intro i hi
    have hi18 : i ≠ 18 := by simpa using hi
    by_cases hi45 : i = 45
    · subst i; exact ht45.trans hready.2.2.1.symm
    have htt := htf.tapes i (by simpa using hi45)
    by_cases hi10 : i = 10
    · subst i; exact htt.trans (h10.trans hready.1.symm)
    by_cases hi11 : i = 11
    · subst i; exact htt.trans (h11.trans hready.2.1.symm)
    exact htt.trans (hf.tapes i (by simp [natWork, hi10, hi11, hi45, hi18]))

/-- Finite, statically known codec shapes. List lengths are read from the
input by the compiled parser and never appear in its machine instructions. -/
inductive Shape where
  | bit
  | nat
  | pair (left right : Shape)
  | list (element : Shape)

def Shape.height : Shape → ℕ
  | .bit | .nat => 0
  | .pair left right => max left.height right.height
  | .list element => element.height+1

@[reducible] def Payload : Shape → Type
  | .bit => Bool
  | .nat => ℕ
  | .pair left right => Payload left × Payload right
  | .list element => List (Payload element)

def wire : (shape : Shape) → Payload shape → List Bool
  | .bit, b => [b]
  | .nat, n => Codec.nat n
  | .pair left right, (x,y) => wire left x ++ wire right y
  | .list element, xs => Codec.list (wire element) xs

/-- Exact atom prices are charged by the interpreter. -/
def atomCost : (shape : Shape) → Payload shape → ℕ
  | .bit, _ => 5
  | .nat, n => 71 * n.bits.length + 67
  | .pair left right, (x,y) => atomCost left x + atomCost right y
  | .list element, xs => (xs.map (atomCost element)).sum

/-- Parsing contract used to compose the fixed target schema. It records
actual structured executions, exact retained bytes, and full tape framing. -/
def Parses (shape : Shape) (code : Code) (depth : ℕ) (price : Payload shape → ℕ) : Prop :=
  depth + shape.height ≤ 14 → ∀ (x : Payload shape) (preceding suffix saved : List Bool) (randomTape : ℕ → Bool)
    (s : Store), s.val.inputHead = preceding.length → Ready depth s.val →
    s.val.tapes 18 = BitTape.atEnd saved →
    ∃ (cost : ℕ) (t : Store),
      Executes (preceding ++ (wire shape x ++ suffix)) randomTape code cost s t ∧ cost ≤ price x ∧
      t.val.inputHead = s.val.inputHead + (wire shape x).length ∧
      t.val.tapes 18 = BitTape.atEnd (saved ++ wire shape x) ∧ Frame {18} s.val t.val

theorem parses_bit (depth : ℕ) : Parses .bit (.call (readBit 18)) depth (fun _ => 5) := by
  intro _ b preceding suffix saved randomTape s hh _ hl
  have h := readBit_steps 18 b preceding suffix saved randomTape s hh hl
  refine ⟨5, Store.ofState (readBitFinish 18 b s.val), h.1, le_rfl, rfl, h.2.1, ?_⟩
  exact ⟨h.2.2.address, h.2.2.memory, h.2.2.randomCursor, h.2.2.output, h.2.2.tapes⟩

theorem parses_nat (depth : ℕ) : Parses .nat natural depth (fun n => 71*n.bits.length+67) := by
  intro _ n preceding suffix saved randomTape s hh hr hl
  obtain ⟨t, ht, hh, hl, hf⟩ := natural_steps depth n preceding suffix saved randomTape s hh hr hl
  exact ⟨_, t, ht, le_rfl, hh, hl, hf⟩

theorem parses_pair (left right : Shape) (first second : Code) (depth : ℕ)
    (p : Payload left → ℕ) (q : Payload right → ℕ)
    (hp : Parses left first depth p) (hq : Parses right second depth q) :
    Parses (.pair left right) (.seq first second) depth (fun x => p x.1 + q x.2) := by
  intro hd x preceding suffix saved randomTape s hh hr hl
  have hdl : depth + left.height ≤ 14 := by dsimp [Shape.height] at hd; omega
  have hdr : depth + right.height ≤ 14 := by dsimp [Shape.height] at hd; omega
  rcases x with ⟨x,y⟩
  obtain ⟨a, u, hu, hca, huh, hul, huf⟩ := hp hdl x preceding (wire right y ++ suffix) saved
    randomTape s hh hr hl
  obtain ⟨b, t, ht, hcb, hth, htl, htf⟩ := hq hdr y (preceding ++ wire left x) suffix
    (saved ++ wire left x) randomTape u (by simp [huh, hh]) (hr.frame huf) hul
  have hi : (preceding ++ wire left x) ++ (wire right y ++ suffix) =
      preceding ++ (wire left x ++ (wire right y ++ suffix)) := by simp [List.append_assoc]
  rw [hi] at ht
  refine ⟨a+b, t, ?_, Nat.add_le_add hca hcb, ?_, ?_, huf.trans htf⟩
  · simpa [wire, List.append_assoc] using hu.seq ht
  · simp only [wire, List.length_append, Nat.cast_add]
    omega
  · simpa [wire, List.append_assoc] using htl

end Maxwell.Cost.DecoderParser
