import Maxwell.Cost.DecoderParser.Replay
import Maxwell.Cost.Array

namespace Maxwell.Cost.DecoderParser

private theorem uniform_flatMap_length {α : Type*} (xs : List α) (f : α → List Bool) (W : ℕ)
    (h : ∀ x ∈ xs, (f x).length=W) : (xs.flatMap f).length=xs.length*W := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    rw [h x (by simp),ih (by intro y hy;exact h y (by simp [hy]))]
    ring

private theorem uniform_flatMap_get {α : Type*} (xs : List α) (f : α → List Bool) (W j i : ℕ)
    (h : ∀ x ∈ xs, (f x).length=W) (hj : j<xs.length) (hi : i<W) :
    (xs.flatMap f)[j*W+i]'(by rw [uniform_flatMap_length xs f W h];nlinarith) =
      (f xs[j])[i]'(by rw [h _ (List.getElem_mem hj)];exact hi) := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : ∀y∈xs,(f y).length=W := by intro y hy;exact h y (by simp [hy])
    cases j with
    | zero =>
      simp only [Nat.zero_mul,Nat.zero_add,List.flatMap_cons,List.getElem_cons_zero]
      rw [List.getElem_append_left (by omega)]
    | succ j =>
      simp only [List.flatMap_cons,List.getElem_cons_succ]
      rw [List.getElem_append_right (by rw [hx];nlinarith)]
      have he : (j+1)*W+i-(f x).length=j*W+i := by rw [hx];simp only [Nat.add_mul,one_mul];omega
      simpa [he] using ih j ht (by simpa using hj)

/-- The actually stored consecutive message memory returns exactly the
requested raw word at address `j * width`, for every possible message. -/
theorem read_message {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (messages : D.Messages) (memory : ℕ → Bool) (j : Fin D.sampleCount) :
    MemoryWord.readBits (MemoryWord.writeBits memory 0 (Codec.messages D messages))
      (j.val*D.format.width) D.format.width = Codec.word D.format (messages j) := by
  apply List.ext_getElem
  · simp [MemoryWord.readBits_length,Codec.word_length]
  · intro i hi hj
    have hiW : i<D.format.width := by simpa using hi
    rw [MemoryWord.readBits_getElem _ _ _ _ hiW]
    have hwithin : j.val*D.format.width+i<(Codec.messages D messages).length := by
      rw [Codec.messages_length]
      nlinarith [j.isLt]
    have hm := MemoryWord.writeBits_inside memory 0 (Codec.messages D messages)
      (j.val*D.format.width+i) hwithin
    simp only [Nat.zero_add] at hm
    rw [hm]
    have hg := uniform_flatMap_get (List.ofFn messages) (Codec.word D.format)
      D.format.width j.val i (by intro x _;exact Codec.word_length _ _) (by simp) hiW
    simpa [Codec.messages] using hg

def messageWords {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (messages : D.Messages) : Vector (List Bool) D.sampleCount :=
  Vector.ofFn (fun j => Codec.word D.format (messages j))

@[simp] theorem messageWords_get {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (messages : D.Messages) (j : Fin D.sampleCount) :
    (messageWords D messages).get j = Codec.word D.format (messages j) := by
  simp [messageWords,Vector.get,Fin.cast]

/-- Loading the actual public message stream constructs precisely the array
layout consumed by the finite indexed-address reader. -/
theorem messages_represent {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (messages : D.Messages) (memory : ℕ → Bool) :
    BitArray.Represents (MemoryWord.writeBits memory 0 (Codec.messages D messages))
      0 D.format.width (messageWords D messages) := by
  refine ⟨fun j => by simp [Codec.word_length], ?_⟩
  intro j i hi
  have h := congrArg (fun bits : List Bool => bits[i]?) (read_message D messages memory j)
  have hm := MemoryWord.readBits_getElem
    (MemoryWord.writeBits memory 0 (Codec.messages D messages)) (j.val*D.format.width)
    D.format.width i hi
  have hw : i < (Codec.word D.format (messages j)).length := by simpa [Codec.word_length] using hi
  have hr : i < (MemoryWord.readBits
      (MemoryWord.writeBits memory 0 (Codec.messages D messages))
      (j.val*D.format.width) D.format.width).length := by simpa using hi
  rw [List.getElem?_eq_getElem hr,List.getElem?_eq_getElem hw] at h
  simp only [Option.some.injEq] at h
  simpa using hm.symm.trans h

private theorem testBits_value (width value : ℕ) (h : value < 2^width) :
    addressValue (List.ofFn (fun i : Fin width => value.testBit i.val)) = value := by
  induction width generalizing value with
  | zero => have hv : value=0 := by simpa using h
            subst value
            rfl
  | succ width ih =>
    rw [List.ofFn_succ]
    simp only [addressValue,Fin.val_zero,Fin.val_succ,Nat.testBit_succ]
    have hhalf : value/2 < 2^width := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa [pow_succ] using h
    rw [ih (value/2) hhalf]
    have hb : (value.testBit 0).toNat=value%2 := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      simp only [pow_zero,Nat.div_one]
      have hm := Nat.mod_lt value (by decide : 0<2)
      by_cases hh : value%2=1
      · simp [hh]
      · have hz : value%2=0 := by omega
        simp [hz]
    rw [hb]
    omega

theorem messageWord_value (F : Target.FixedPointFormat) (w : F.Word) :
    addressValue (Codec.word F w)=w.val := testBits_value F.width w.val w.isLt

end Maxwell.Cost.DecoderParser
