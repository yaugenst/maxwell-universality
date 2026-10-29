import Maxwell.Cost.PhysicalMaterial.ScatterRow
import Maxwell.Cost.PhysicalMaterial.ScatterSpec
import Maxwell.Cost.Structured.CountedShifted

namespace Maxwell.Cost.PhysicalMaterial.Scatter
open Structured RationalAccumulator
set_option maxHeartbeats 2400000

def passWork : Finset ℕ := recordWork ∪ {303}
structure PassFrame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i = 4 ∨ 10 ≤ i → i ∉ passWork → t.tapes i = s.tapes i

theorem PassFrame.refl (s : BitRAMState) : PassFrame s s := ⟨rfl,rfl,rfl,fun _ _ _ => rfl⟩
theorem PassFrame.trans {s t u : BitRAMState} (h : PassFrame s t) (k : PassFrame t u) : PassFrame s u :=
  ⟨k.inputHead.trans h.inputHead,k.randomCursor.trans h.randomCursor,k.output.trans h.output,
    fun i hi hn => (k.tapes i hi hn).trans (h.tapes i hi hn)⟩

def PassInvariant {n cells : ℕ} (d : Descriptors.Data n) (l : Dense.Layout cells)
    (points : List Point) (locations : Fin n → Point → Fin cells)
    (nums dens : Vector (List Bool) cells) (ny nz B : ℕ) (initial : BitRAMState)
    (remaining : ℕ) (s : Store) : Prop :=
  remaining ≤ n ∧ ∃ index : List Bool,
    addressValue index = n-remaining ∧ index.length ≤ B ∧ BankArray.Word s.val 302 index ∧
    PointReady s.val ∧ Descriptors.Stored d s.val ∧ Descriptors.Bank s.val (fun _ => 0) ∧
    Dense.Stored l (filledNums d l points locations nums (n-remaining))
      (filledDens d l points locations dens (n-remaining)) s.val ∧
    Word s.val 251 ny ∧ Word s.val 252 nz ∧ PassFrame initial s.val ∧ Dense.Outside l initial s.val

private theorem pass_stable {n cells : ℕ} (d : Descriptors.Data n) (l : Dense.Layout cells)
    (points : List Point) (locations : Fin n → Point → Fin cells)
    (nums dens : Vector (List Bool) cells) (ny nz B : ℕ) (initial : BitRAMState)
    (remaining : ℕ) (s t : Store) (hf : CountedShifted.Frame 303 s t)
    (hs : PassInvariant d l points locations nums dens ny nz B initial remaining s) :
    PassInvariant d l points locations nums dens ny nz B initial remaining t := by
  obtain ⟨hr,index,hi,hil,hindex,hready,hd,hbank,hl,hny,hnz,hframe,houtside⟩ := hs
  have keep := hf.2.2.2.2.2.1
  have frame : PassFrame s.val t.val :=
    ⟨hf.2.1,hf.2.2.2.1,hf.2.2.2.2.1,fun j _ hj => keep j (by
      intro he; subst j; exact hj (by simp [passWork]))⟩
  refine ⟨hr,index,hi,hil,BankArray.word_of_eq (keep 302 (by decide)) hindex,?_,?_,?_,?_,
    word_of_eq (keep 251 (by decide)) hny,word_of_eq (keep 252 (by decide)) hnz,
    hframe.trans frame,houtside.trans (Dense.Outside.of_memory l hf.2.2.1)⟩
  · exact ⟨(fun j hj => blank_of_eq (keep j (by omega)) (hready.1 j hj)),
      blank_of_eq (keep 37 (by decide)) hready.2.1,
      blank_of_eq (keep 292 (by decide)) hready.2.2.1,
      blank_of_eq (keep 322 (by decide)) hready.2.2.2.1,
      fun j => blank_of_eq (keep (324+j.val) (by omega)) (hready.2.2.2.2 j)⟩
  · refine ⟨BankArray.word_of_eq (keep 300 (by decide)) hd.width,
      BankArray.word_of_eq (keep 301 (by decide)) hd.clock,?_,?_⟩
    · intro j
      exact BankArray.word_of_eq (keep (Descriptors.baseTape j) (by simp only [Descriptors.baseTape]; omega)) (hd.bases j)
    · intro j
      simpa only [hf.2.2.1] using hd.arrays j
  · intro j
    exact word_of_eq (keep (Descriptors.targetTape j) (by have := Descriptors.targetTape_bounds j; omega)) (hbank j)
  · exact ⟨BankArray.word_of_eq (keep 300 (by decide)) hl.width,
      BankArray.word_of_eq (keep 301 (by decide)) hl.clock,
      BankArray.word_of_eq (keep 320 (by decide)) hl.numBase,
      BankArray.word_of_eq (keep 321 (by decide)) hl.denBase,
      by simpa only [hf.2.2.1] using hl.nums,by simpa only [hf.2.2.1] using hl.dens⟩

def scanCode (points : List Point) : Code := .seq (CountedShifted.code 303 (recordCode points))
  (.seq (.call (TapeOps.clear 303)) (.call (TapeOps.clear 302)))
def scanBudget (n B : ℕ) (points : List Point) : ℕ :=
  (n+1)*(13*B+15)+n*recordBudget points B+12*B+8

/-- Each actual descriptor is read once. The fixed prototype is scattered at
runtime-computed addresses, and the loop restores its two control tapes. -/
theorem scan {n cells : ℕ} (d : Descriptors.Data n) (l : Dense.Layout cells)
    (points : List Point) (locations : Fin n → Point → Fin cells)
    (nums dens : Vector (List Bool) cells) (ny nz B : ℕ)
    (hd : d.Sized B) (hl : l.Sized B) (hwidth : d.width = l.width)
    (hsep : SeparatedData d l) (hn : n < 2^B) (hcells : cells < 2^B)
    (hindex : ∀ i p, p ∈ points → flatIndex (anchor d i) p ny nz = (locations i p).val)
    (hroom : ∀ i p, p ∈ points → ∀ j, 0 ≤ (anchor d i j : ℤ)+p j)
    (hnyB : ny.bits.length ≤ B) (hnzB : nz.bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (index count : List Bool)
    (hi : addressValue index = 0) (hc : addressValue count = n)
    (hil : index.length ≤ B) (hcl : count.length ≤ B) (origin : ℤ) (s : Store)
    (hs : PointReady s.val) (hdata : Descriptors.Stored d s.val)
    (hdense : Dense.Stored l nums dens s.val)
    (hsi : BankArray.Word s.val 302 index) (hcounter : s.val.tapes 303 = BitTape.shifted count origin)
    (hbank : Descriptors.Bank s.val (fun _ => 0)) (hny : Word s.val 251 ny) (hnz : Word s.val 252 nz) :
    ∃ cost t, cost ≤ scanBudget n B points ∧ Executes input tape (scanCode points) cost s t ∧
      PointReady t.val ∧ Descriptors.Stored d t.val ∧ Descriptors.Bank t.val (fun _ => 0) ∧
      Dense.Stored l (filledNums d l points locations nums n) (filledDens d l points locations dens n) t.val ∧
      Blank t.val 302 ∧ Blank t.val 303 ∧ PassFrame s.val t.val ∧ Dense.Outside l s.val t.val := by
  let inv := PassInvariant d l points locations nums dens ny nz B s.val
  have body : ∀ r xs u, inv (r+1) u → u.val.tapes 303 = BitTape.shifted xs origin →
      addressValue xs = r → ∃ bodyCost t, Executes input tape (recordCode points) bodyCost u t ∧
        inv r t ∧ t.val.tapes 303 = BitTape.shifted xs origin ∧ bodyCost ≤ recordBudget points B := by
    intro r xs u hu hcounter _
    obtain ⟨hr,index,hi,hil,hui,hur,hud,hub,hul,huny,hunz,huf,huo⟩ := hu
    let i : Fin n := ⟨n-(r+1),by omega⟩
    obtain ⟨cost,t,hcost,he,htr,htd,htb,htl,hti,htf,hto⟩ := record d l points locations _ _ ny nz B
      hd hl hwidth hsep hcells i (hindex i) (hroom i) hnyB hnzB input tape index hi hil u hur hud hul hui hub huny hunz
    have hnext : n-r = i.val+1 := by dsimp only [i]; omega
    have hlen : (Increment.bits index).length ≤ B := BankArray.increment_length_bound index B hil
      (by rw [hi]; dsimp only [i] at hnext; omega)
    have hf : PassFrame u.val t.val :=
      ⟨htf.inputHead,htf.randomCursor,htf.output,fun j hj hn => htf.tapes j hj (fun hm => hn (Finset.mem_union_left _ hm))⟩
    refine ⟨cost,t,he,⟨by omega,Increment.bits index,?_,hlen,hti,htr,htd,htb,?_,
      word_of_eq (htf.tapes 251 (by omega) (by decide)) huny,
      word_of_eq (htf.tapes 252 (by omega) (by decide)) hunz,huf.trans hf,huo.trans hto⟩,
      (htf.tapes 303 (by omega) (by decide)).trans hcounter,hcost⟩
    · rw [Increment.bits_value,hi]
      dsimp only [i] at hnext
      omega
    · rw [hnext,filledNums_step,filledDens_step]
      exact htl
  have initial : inv n s := by
    refine ⟨le_rfl,index,by simpa using hi,hil,hsi,hs,hdata,hbank,?_,hny,hnz,.refl _,.refl _ _⟩
    simpa only [Nat.sub_self,filledNums_zero,filledDens_zero] using hdense
  obtain ⟨cost,a,finalCount,ea,hai,hac,hal,_,hab⟩ := CountedShifted.executes
    303 origin (recordCode points) input tape inv (fun _ => recordBudget points B)
    (pass_stable d l points locations nums dens ny nz B s.val) body n count s hc hcounter initial
  obtain ⟨_,finalIndex,_,hfil,⟨io,hio⟩,har,had,hav,halocal,_,_,haf,hao⟩ := hai
  obtain ⟨b,eb,hbt,fb⟩ := WordCall.clear 303 input tape finalCount origin a hac
  have hbi : b.val.tapes 302 = BitTape.shifted finalIndex io := by simpa [hbt] using hio
  obtain ⟨t,et,htt,ft⟩ := WordCall.clear 302 input tape finalIndex io b hbi
  have keep (j : ℕ) (h302 : j ≠ 302) (h303 : j ≠ 303) : t.val.tapes j = a.val.tapes j := by
    simp [htt,hbt,h302,h303]
  have frame : PassFrame a.val t.val := by
    refine ⟨ft.2.1.trans fb.2.1,ft.2.2.2.1.trans fb.2.2.2.1,ft.2.2.2.2.1.trans fb.2.2.2.2.1,?_⟩
    intro j _ hj
    apply keep j
    · intro heq; subst j; exact hj (by decide)
    · intro heq; subst j; exact hj (by decide)
  have hm : t.val.memory = a.val.memory := ft.2.2.1.trans fb.2.2.1
  refine ⟨cost+((6*finalCount.length+4)+(6*finalIndex.length+4)),t,?_,ea.seq (eb.seq et),?_,?_,?_,?_,
    ⟨io+finalIndex.length,by simp [htt]⟩,⟨origin+finalCount.length,by simp [htt,hbt]⟩,
    haf.trans frame,hao.trans (Dense.Outside.of_memory l hm)⟩
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at hab
    have hcountercost : (n+1)*(13*count.length+15) ≤ (n+1)*(13*B+15) := by gcongr
    dsimp only [scanBudget]
    omega
  · exact ⟨(fun j hj => blank_of_eq (keep j (by omega) (by omega)) (har.1 j hj)),
      blank_of_eq (keep 37 (by decide) (by decide)) har.2.1,
      blank_of_eq (keep 292 (by decide) (by decide)) har.2.2.1,
      blank_of_eq (keep 322 (by decide) (by decide)) har.2.2.2.1,
      fun j => blank_of_eq (keep (324+j.val) (by omega) (by omega)) (har.2.2.2.2 j)⟩
  · refine ⟨BankArray.word_of_eq (keep 300 (by decide) (by decide)) had.width,
      BankArray.word_of_eq (keep 301 (by decide) (by decide)) had.clock,?_,?_⟩
    · intro j
      exact BankArray.word_of_eq (keep (Descriptors.baseTape j) (by simp only [Descriptors.baseTape]; omega)
        (by simp only [Descriptors.baseTape]; omega)) (had.bases j)
    · intro j
      simpa only [hm] using had.arrays j
  · intro j
    exact word_of_eq (keep (Descriptors.targetTape j) (by have := Descriptors.targetTape_bounds j; omega)
      (by have := Descriptors.targetTape_bounds j; omega)) (hav j)
  · simp only [Nat.sub_zero] at halocal
    exact ⟨BankArray.word_of_eq (keep 300 (by decide) (by decide)) halocal.width,
      BankArray.word_of_eq (keep 301 (by decide) (by decide)) halocal.clock,
      BankArray.word_of_eq (keep 320 (by decide) (by decide)) halocal.numBase,
      BankArray.word_of_eq (keep 321 (by decide) (by decide)) halocal.denBase,
      by simpa only [hm] using halocal.nums,by simpa only [hm] using halocal.dens⟩

end Maxwell.Cost.PhysicalMaterial.Scatter
