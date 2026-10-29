import Maxwell.Cost.PhysicalMaterial.DenseInitRow
import Maxwell.Cost.Structured.CountedShifted
import Maxwell.Cost.BinaryPrecision

/-! Dense strength arrays are initialized by an actual stored-count loop.
The previous contents are recovered from actual memory, never assumed zero. -/
namespace Maxwell.Cost.PhysicalMaterial.DenseInit
open Structured RationalAccumulator
open scoped BigOperators
set_option maxHeartbeats 1500000

private def Invariant {n : ℕ} (l : Dense.Layout n) (nums dens : Vector (List Bool) n)
    (B : ℕ) (initial : BitRAMState) (remaining : ℕ) (s : Store) : Prop :=
  remaining ≤ n ∧ ∃ index : List Bool,
    addressValue index = n-remaining ∧ index.length ≤ B ∧ BankArray.Word s.val 322 index ∧
    Descriptors.Ready s.val ∧ Blank s.val 37 ∧
    Dense.Stored l
      (Dense.filled nums (FixedWidth.bits (addressValue l.width) (0:ℕ).bits) (n-remaining))
      (Dense.filled dens (FixedWidth.bits (addressValue l.width) (1:ℕ).bits) (n-remaining)) s.val ∧
    Word s.val 276 0 ∧ Word s.val 277 1 ∧ Dense.InitFrame initial s.val ∧ Dense.Outside l initial s.val

private theorem stable {n : ℕ} (l : Dense.Layout n) (nums dens : Vector (List Bool) n)
    (B : ℕ) (initial : BitRAMState) (remaining : ℕ) (s t : Store)
    (hf : CountedShifted.Frame 329 s t) (hs : Invariant l nums dens B initial remaining s) :
    Invariant l nums dens B initial remaining t := by
  obtain ⟨hr,index,hi,hil,hindex,hready,h37,hd,h0,h1,hframe,houtside⟩ := hs
  have keep := hf.2.2.2.2.2.1
  have frame : Dense.InitFrame s.val t.val :=
    ⟨hf.2.1,hf.2.2.2.1,hf.2.2.2.2.1,fun j _ _ _ hj => keep j hj⟩
  refine ⟨hr,index,hi,hil,BankArray.word_of_eq (keep 322 (by decide)) hindex,
    (fun j hj => blank_of_eq (keep j (by omega)) (hready j hj)),
    blank_of_eq (keep 37 (by decide)) h37,?_,
    word_of_eq (keep 276 (by decide)) h0,word_of_eq (keep 277 (by decide)) h1,
    hframe.trans frame,houtside.trans (Dense.Outside.of_memory l hf.2.2.1)⟩
  exact ⟨BankArray.word_of_eq (keep 300 (by decide)) hd.width,
    BankArray.word_of_eq (keep 301 (by decide)) hd.clock,
    BankArray.word_of_eq (keep 320 (by decide)) hd.numBase,
    BankArray.word_of_eq (keep 321 (by decide)) hd.denBase,
    by simpa only [hf.2.2.1] using hd.nums,by simpa only [hf.2.2.1] using hd.dens⟩

def scanCode : Code := .seq (CountedShifted.code 329 Dense.initRowCode)
  (.seq (.call (TapeOps.clear 329)) (.call (TapeOps.clear 322)))

def scanBudget (n B : ℕ) : ℕ :=
  (n+1)*(13*B+15)+n*(81000*(B+2)^2)+12*B+8

/-- The fixed countdown initializes every slot and then erases both control
words. The incremented index is an actual tape word throughout the loop. -/
theorem scan {n : ℕ} (l : Dense.Layout n) (nums dens : Vector (List Bool) n)
    (B : ℕ) (hl : l.Sized B) (hn : n < 2^B) (input : List Bool) (tape : ℕ → Bool)
    (index count : List Bool) (hi : addressValue index = 0) (hc : addressValue count = n)
    (hil : index.length ≤ B) (hcl : count.length ≤ B) (origin : ℤ) (s : Store)
    (hs : Descriptors.Ready s.val) (h37 : Blank s.val 37) (hd : Dense.Stored l nums dens s.val)
    (hindex : BankArray.Word s.val 322 index) (hcounter : s.val.tapes 329 = BitTape.shifted count origin)
    (h0 : Word s.val 276 0) (h1 : Word s.val 277 1) :
    ∃ cost t, cost ≤ scanBudget n B ∧ Executes input tape scanCode cost s t ∧
      Descriptors.Ready t.val ∧ Blank t.val 37 ∧
      Dense.Stored l
        (Vector.replicate n (FixedWidth.bits (addressValue l.width) (0:ℕ).bits))
        (Vector.replicate n (FixedWidth.bits (addressValue l.width) (1:ℕ).bits)) t.val ∧
      Word t.val 276 0 ∧ Word t.val 277 1 ∧ Blank t.val 322 ∧ Blank t.val 329 ∧
      Dense.InitFrame s.val t.val ∧ Dense.Outside l s.val t.val := by
  let inv := Invariant l nums dens B s.val
  have body : ∀ r xs u, inv (r+1) u → u.val.tapes 329 = BitTape.shifted xs origin →
      addressValue xs = r → ∃ bodyCost t, Executes input tape Dense.initRowCode bodyCost u t ∧
        inv r t ∧ t.val.tapes 329 = BitTape.shifted xs origin ∧ bodyCost ≤ 81000*(B+2)^2 := by
    intro r xs u hu hcounter _
    obtain ⟨hr,index,hi,hil,hindex,hur,hu37,hud,hu0,hu1,huf,huo⟩ := hu
    let i : Fin n := ⟨n-(r+1),by omega⟩
    obtain ⟨cost,t,hcost,he,htr,ht37,htd,hti,ht329,htf,hto⟩ := Dense.init_row l _ _ i B hl
      input tape index hi hil u hur hu37 hud hindex hu0 hu1
    have hnext : n-r = i.val+1 := by dsimp only [i]; omega
    have hlen : (Increment.bits index).length ≤ B := BankArray.increment_length_bound index B hil
      (by rw [hi]; dsimp only [i] at hnext; omega)
    refine ⟨cost,t,he,⟨by omega,Increment.bits index,?_,hlen,hti,htr,ht37,?_,
      word_of_eq (htf.tapes 276 (by decide) (by decide) (by decide) (by decide)) hu0,
      word_of_eq (htf.tapes 277 (by decide) (by decide) (by decide) (by decide)) hu1,
      huf.trans htf,huo.trans hto⟩,ht329.trans hcounter,hcost⟩
    · rw [Increment.bits_value,hi]
      dsimp only [i] at hnext
      omega
    · rw [hnext]
      rw [← Dense.filled_step nums _ i,← Dense.filled_step dens _ i]
      exact htd
  have initial : inv n s := by
    refine ⟨le_rfl,index,by simpa using hi,hil,hindex,hs,h37,?_,h0,h1,.refl _,.refl _ _⟩
    simpa only [Nat.sub_self,Dense.filled_zero] using hd
  obtain ⟨cost,a,finalCount,ea,hai,hac,hal,_,hab⟩ := CountedShifted.executes
    329 origin Dense.initRowCode input tape inv (fun _ => 81000*(B+2)^2)
    (stable l nums dens B s.val) body n count s hc hcounter initial
  obtain ⟨_,finalIndex,_,hfil,⟨io,hio⟩,har,ha37,had,ha0,ha1,haf,hao⟩ := hai
  obtain ⟨b,eb,hbt,fb⟩ := WordCall.clear 329 input tape finalCount origin a hac
  have hbi : b.val.tapes 322 = BitTape.shifted finalIndex io := by simpa [hbt] using hio
  obtain ⟨t,et,htt,ft⟩ := WordCall.clear 322 input tape finalIndex io b hbi
  have keep (j : ℕ) (h322 : j ≠ 322) (h329 : j ≠ 329) : t.val.tapes j = a.val.tapes j := by
    simp [htt,hbt,h322,h329]
  have frame : Dense.InitFrame a.val t.val :=
    ⟨ft.2.1.trans fb.2.1,ft.2.2.2.1.trans fb.2.2.2.1,ft.2.2.2.2.1.trans fb.2.2.2.2.1,
      fun j _ _ h322 h329 => keep j h322 h329⟩
  have hm : t.val.memory = a.val.memory := ft.2.2.1.trans fb.2.2.1
  refine ⟨cost+((6*finalCount.length+4)+(6*finalIndex.length+4)),t,?_,ea.seq (eb.seq et),
    (fun j hj => blank_of_eq (keep j (by omega) (by omega)) (har j hj)),
    blank_of_eq (keep 37 (by decide) (by decide)) ha37,?_,
    word_of_eq (keep 276 (by decide) (by decide)) ha0,word_of_eq (keep 277 (by decide) (by decide)) ha1,
    ⟨io+finalIndex.length,by simp [htt]⟩,⟨origin+finalCount.length,by simp [htt,hbt]⟩,
    haf.trans frame,hao.trans (Dense.Outside.of_memory l hm)⟩
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at hab
    have hcountercost : (n+1)*(13*count.length+15) ≤ (n+1)*(13*B+15) := by gcongr
    dsimp only [scanBudget]
    omega
  · have finalStored : Dense.Stored l
        (Vector.replicate n (FixedWidth.bits (addressValue l.width) (0:ℕ).bits))
        (Vector.replicate n (FixedWidth.bits (addressValue l.width) (1:ℕ).bits)) a.val := by
      simpa only [Nat.sub_zero,Dense.filled_all] using had
    exact ⟨BankArray.word_of_eq (keep 300 (by decide) (by decide)) finalStored.width,
      BankArray.word_of_eq (keep 301 (by decide) (by decide)) finalStored.clock,
      BankArray.word_of_eq (keep 320 (by decide) (by decide)) finalStored.numBase,
      BankArray.word_of_eq (keep 321 (by decide) (by decide)) finalStored.denBase,
      by simpa only [hm] using finalStored.nums,by simpa only [hm] using finalStored.dens⟩

/-- Metadata is sufficient before initialization; no representation premise
is required for either target array. -/
structure Metadata {n : ℕ} (l : Dense.Layout n) (s : BitRAMState) : Prop where
  width : BankArray.Word s 300 l.width
  clock : BankArray.Word s 301 l.clock
  numBase : BankArray.Word s 320 l.numBase
  denBase : BankArray.Word s 321 l.denBase

structure Frame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ j, j = 4 ∨ 10 ≤ j → j ≠ 37 → j ≠ 277 → j ≠ 322 → j ≠ 329 →
    t.tapes j = s.tapes j

def code : Code := .seq (BinaryPrecision.literalCode 277 1)
  (.seq (.call (WordTransfer.clone 328 329)) (.seq scanCode (.call (TapeOps.clear 277))))

def costBound (n B : ℕ) : ℕ := scanBudget n B+15*B+44

/-- Initialize the actual two dense arrays from arbitrary memory by cloning
the stored cell count, writing zero/one in every slot, and reclaiming all
initialization controls. Memory outside the two arrays is unchanged. -/
theorem executes {n : ℕ} (l : Dense.Layout n) (B : ℕ) (hl : l.Sized B) (hn : n < 2^B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : Descriptors.Ready s.val)
    (hmeta : Metadata l s.val) (hcount : Word s.val 328 n)
    (h37 : Blank s.val 37) (h276 : Blank s.val 276) (h277 : Blank s.val 277)
    (h322 : Blank s.val 322) (h329 : Blank s.val 329) :
    ∃ cost t, cost ≤ costBound n B ∧ Executes input tape code cost s t ∧
      Descriptors.Ready t.val ∧ Blank t.val 37 ∧ Blank t.val 276 ∧ Blank t.val 277 ∧
      Blank t.val 322 ∧ Blank t.val 329 ∧
      Dense.Stored l
        (Vector.replicate n (FixedWidth.bits (addressValue l.width) (0:ℕ).bits))
        (Vector.replicate n (FixedWidth.bits (addressValue l.width) (1:ℕ).bits)) t.val ∧
      Frame s.val t.val ∧ Dense.Outside l s.val t.val := by
  have hnlen : n.bits.length ≤ B := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hn
  let nums := Dense.snapshot s.val.memory (addressValue l.numBase) (addressValue l.width) n
  let dens := Dense.snapshot s.val.memory (addressValue l.denBase) (addressValue l.width) n
  obtain ⟨a,e1,ha277,f1⟩ := BinaryPrecision.literal 277 1 input tape s h277
  obtain ⟨countOrigin,hcountWord⟩ := hcount
  obtain ⟨counterOrigin,hcounterBlank⟩ := h329
  obtain ⟨b,e2,hbt,f2⟩ := WordCall.clone 328 329 (by decide) input tape n.bits countOrigin
    counterOrigin a ((f1.tapes 328 (by simp)).trans hcountWord)
    ((f1.tapes 329 (by simp)).trans hcounterBlank)
  have keepb (j : ℕ) (h329 : j ≠ 329) : b.val.tapes j = a.val.tapes j := by simp [hbt,h329]
  have keep (j : ℕ) (h277 : j ≠ 277) (h329 : j ≠ 329) : b.val.tapes j = s.val.tapes j :=
    (keepb j h329).trans (f1.tapes j (by simpa using h277))
  have hbmem : b.val.memory = s.val.memory := f2.2.2.1.trans f1.memory
  have hbready : Descriptors.Ready b.val := fun j hj => blank_of_eq (keep j (by omega) (by omega)) (hs j hj)
  have hbStored : Dense.Stored l nums dens b.val :=
    ⟨BankArray.word_of_eq (keep 300 (by decide) (by decide)) hmeta.width,
      BankArray.word_of_eq (keep 301 (by decide) (by decide)) hmeta.clock,
      BankArray.word_of_eq (keep 320 (by decide) (by decide)) hmeta.numBase,
      BankArray.word_of_eq (keep 321 (by decide) (by decide)) hmeta.denBase,
      by rw [hbmem]; exact Dense.snapshot_represents _ _ _ _,
      by rw [hbmem]; exact Dense.snapshot_represents _ _ _ _⟩
  have hbindex : BankArray.Word b.val 322 [] := by
    obtain ⟨origin,ho⟩ := h322
    exact ⟨origin,by simpa using (keep 322 (by decide) (by decide)).trans ho⟩
  obtain ⟨c3,c,hc3,e3,hcr,hc37,hcd,hc0,hc1,hc322,hc329,f3,o3⟩ := scan l nums dens B hl hn
    input tape [] n.bits rfl (by simp) (by simp) hnlen counterOrigin b hbready
    (blank_of_eq (keep 37 (by decide) (by decide)) h37) hbStored hbindex (by simp [hbt])
    ((zero_word_iff_blank _ _).mpr (blank_of_eq (keep 276 (by decide) (by decide)) h276))
    (word_of_eq (keepb 277 (by decide)) ha277)
  obtain ⟨oneOrigin,hcOne⟩ := hc1
  obtain ⟨t,e4,htt,f4⟩ := WordCall.clear 277 input tape (1:ℕ).bits oneOrigin c hcOne
  have keept (j : ℕ) (h277 : j ≠ 277) : t.val.tapes j = c.val.tapes j := by simp [htt,h277]
  have htmem : t.val.memory = c.val.memory := f4.2.2.1
  refine ⟨_,t,?_,e1.seq (e2.seq (e3.seq e4)),
    (fun j hj => blank_of_eq (keept j (by omega)) (hcr j hj)),
    blank_of_eq (keept 37 (by decide)) hc37,
    (zero_word_iff_blank _ _).mp (word_of_eq (keept 276 (by decide)) hc0),
    ⟨oneOrigin+(1:ℕ).bits.length,by simp [htt]⟩,
    blank_of_eq (keept 322 (by decide)) hc322,blank_of_eq (keept 329 (by decide)) hc329,?_,?_,
    ((Dense.Outside.of_memory l hbmem).trans o3).trans (Dense.Outside.of_memory l htmem)⟩
  · have hbits1 : (1:ℕ).bits.length = 1 := by decide
    rw [hbits1]
    dsimp only [costBound]
    omega
  · exact ⟨BankArray.word_of_eq (keept 300 (by decide)) hcd.width,
      BankArray.word_of_eq (keept 301 (by decide)) hcd.clock,
      BankArray.word_of_eq (keept 320 (by decide)) hcd.numBase,
      BankArray.word_of_eq (keept 321 (by decide)) hcd.denBase,
      by simpa only [htmem] using hcd.nums,by simpa only [htmem] using hcd.dens⟩
  · exact ⟨f4.2.1.trans (f3.inputHead.trans (f2.2.1.trans f1.inputHead)),
      f4.2.2.2.1.trans (f3.randomCursor.trans (f2.2.2.2.1.trans f1.randomCursor)),
      f4.2.2.2.2.1.trans (f3.output.trans (f2.2.2.2.2.1.trans f1.output)),
      fun j hj h37 h277 h322 h329 => (keept j h277).trans
        ((f3.tapes j hj h37 h322 h329).trans (keep j h277 h329))⟩

theorem costBound_polynomial (n B : ℕ) : costBound n B ≤ 82000*(n+1)*(B+2)^2 := by
  dsimp [costBound,scanBudget]
  nlinarith [Nat.zero_le (n*B^2),Nat.zero_le (B^2)]

end Maxwell.Cost.PhysicalMaterial.DenseInit
