import Maxwell.Cost.PhysicalMaterial.DenseVolume
import Maxwell.Cost.PhysicalMaterial.DenseInit
import Maxwell.Cost.PhysicalMaterial.ScatterRun
import Maxwell.Cost.PhysicalMaterial.ScatterMeaning

namespace Maxwell.Cost.PhysicalMaterial.Preprocess
open Structured RationalAccumulator
set_option maxHeartbeats 2200000

def work : Finset ℕ := Scatter.passWork ∪ {328,329}
structure Frame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ j, j=4 ∨ 10≤j → j∉work → t.tapes j=s.tapes j

def code (points : List Scatter.Point) : Code :=
  .seq DenseVolume.code (.seq DenseInit.code (Scatter.code points))
def costBound (cells n B : ℕ) (points : List Scatter.Point) : ℕ :=
  21000*(B+2)^2+DenseInit.costBound cells B+Scatter.costBound n B points

/-- Allocate actual default strengths from arbitrary memory, then scatter the
actual descriptor records once. The cell count itself is computed from the
three stored dimensions, not supplied by a host material array. -/
theorem executes {n : ℕ} (d : Descriptors.Data n) (nx ny nz B : ℕ)
    (l : Dense.Layout (nx*ny*nz)) (points : List Scatter.Point)
    (locations : Fin n → Scatter.Point → Fin (nx*ny*nz))
    (hd : d.Sized B) (hl : l.Sized B) (hwidth : d.width=l.width)
    (hsep : Scatter.SeparatedData d l) (hn : n<2^B) (hvolume : nx*ny*nz<2^B)
    (hindex : ∀ i p, p∈points → Scatter.flatIndex (Scatter.anchor d i) p ny nz=(locations i p).val)
    (hroom : ∀ i p, p∈points → ∀ j, 0≤(Scatter.anchor d i j:ℤ)+p j)
    (hsize : nx.bits.length≤B ∧ ny.bits.length≤B ∧ nz.bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Scatter.PointReady s.val) (hdata : Descriptors.Stored d s.val)
    (hmeta : DenseInit.Metadata l s.val) (hbank : Descriptors.Bank s.val (fun _ => 0))
    (h302 : Blank s.val 302) (h303 : Blank s.val 303) (h328 : Blank s.val 328) (h329 : Blank s.val 329)
    (hcount : Word s.val 304 n) (hx : Word s.val 250 nx) (hy : Word s.val 251 ny) (hz : Word s.val 252 nz) :
    ∃ cost t, cost≤costBound (nx*ny*nz) n B points ∧ Executes input tape (code points) cost s t ∧
      Scatter.PointReady t.val ∧ Descriptors.Stored d t.val ∧ Descriptors.Bank t.val (fun _=>0) ∧
      Dense.Stored l
        (Scatter.filledNums d l points locations (Scatter.zeroNums l) n)
        (Scatter.filledDens d l points locations (Scatter.oneDens l) n) t.val ∧
      Blank t.val 302 ∧ Blank t.val 303 ∧ Blank t.val 329 ∧ Word t.val 328 (nx*ny*nz) ∧
      Frame s.val t.val ∧ Dense.Outside l s.val t.val := by
  obtain ⟨vc,a,hvc,ev,havol,ha322,har,fa,_⟩ := DenseVolume.executes input tape nx ny nz B s
    hx hy hz (hbank 3) hsize hs.1 hs.2.2.2.1 h328
  have hameta : DenseInit.Metadata l a.val :=
    ⟨BankArray.word_of_eq (fa.tapes 300 (by decide)) hmeta.width,
      BankArray.word_of_eq (fa.tapes 301 (by decide)) hmeta.clock,
      BankArray.word_of_eq (fa.tapes 320 (by decide)) hmeta.numBase,
      BankArray.word_of_eq (fa.tapes 321 (by decide)) hmeta.denBase⟩
  have hav (j : Fin 5) : Word a.val (Descriptors.targetTape j) 0 :=
    word_of_eq (fa.tapes (Descriptors.targetTape j) (by fin_cases j <;> decide)) (hbank j)
  have had : Descriptors.Stored d a.val := by
    refine ⟨BankArray.word_of_eq (fa.tapes 300 (by decide)) hdata.width,
      BankArray.word_of_eq (fa.tapes 301 (by decide)) hdata.clock,?_,?_⟩
    · intro j
      exact BankArray.word_of_eq (fa.tapes (Descriptors.baseTape j) (by
        simp only [Descriptors.baseTape,DenseVolume.work,Finset.mem_insert,Finset.mem_singleton]; omega)) (hdata.bases j)
    · intro j
      simpa only [fa.memory] using hdata.arrays j
  obtain ⟨ic,b,hic,ei,hbr,hb37,hb276,hb277,hb322,hb329,hbl,fb,ob⟩ := DenseInit.executes l B hl hvolume
    input tape a har hameta havol (blank_of_eq (fa.tapes 37 (by decide)) hs.2.1)
    ((zero_word_iff_blank _ _).mp (hav 3)) ((zero_word_iff_blank _ _).mp (hav 4))
    ha322 (blank_of_eq (fa.tapes 329 (by decide)) h329)
  have hbd : Descriptors.Stored d b.val := Scatter.preserve_descriptors d l hsep had ob
    (fun j hj => fb.tapes j (by omega) (by omega) (by omega) (by omega) (by omega))
  have hbp : Scatter.PointReady b.val :=
    ⟨hbr,hb37,
      blank_of_eq ((fb.tapes 292 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (fa.tapes 292 (by decide))) hs.2.2.1,hb322,
      fun j => blank_of_eq ((fb.tapes (324+j.val) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        (fa.tapes (324+j.val) (by simp only [DenseVolume.work,Finset.mem_insert,Finset.mem_singleton]; omega))) (hs.2.2.2.2 j)⟩
  have hbv : Descriptors.Bank b.val (fun _=>0) := by
    intro j
    fin_cases j
    · exact word_of_eq (fb.tapes 294 (by decide) (by decide) (by decide) (by decide) (by decide)) (hav 0)
    · exact word_of_eq (fb.tapes 295 (by decide) (by decide) (by decide) (by decide) (by decide)) (hav 1)
    · exact word_of_eq (fb.tapes 296 (by decide) (by decide) (by decide) (by decide) (by decide)) (hav 2)
    · exact (zero_word_iff_blank _ _).mpr hb276
    · exact (zero_word_iff_blank _ _).mpr hb277
  have keepb (j : ℕ) (hj : j=4 ∨ 10≤j) (h37 : j≠37) (h277 : j≠277)
      (h322 : j≠322) (h328 : j≠328) (h329 : j≠329) : b.val.tapes j=s.val.tapes j :=
    (fb.tapes j hj h37 h277 h322 h329).trans
      (fa.tapes j (by simp only [DenseVolume.work,Finset.mem_insert,Finset.mem_singleton]; omega))
  obtain ⟨sc,t,hsc,es,htr,htd,htv,htl,ht302,ht303,ft,ot⟩ := Scatter.executes d l points locations
    (Scatter.zeroNums l) (Scatter.oneDens l) ny nz B hd hl hwidth hsep hn hvolume hindex hroom
    hsize.2.1 hsize.2.2 input tape b hbp hbd hbl
    (blank_of_eq (keepb 302 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) h302)
    (blank_of_eq (keepb 303 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) h303)
    (word_of_eq (keepb 304 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hcount) hbv
    (word_of_eq (keepb 251 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hy)
    (word_of_eq (keepb 252 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hz)
  refine ⟨vc+(ic+sc),t,by dsimp only [costBound]; omega,ev.seq (ei.seq es),htr,htd,htv,htl,ht302,ht303,
    blank_of_eq (ft.tapes 329 (by decide) (by decide)) hb329,
    word_of_eq ((ft.tapes 328 (by decide) (by decide)).trans
      (fb.tapes 328 (by decide) (by decide) (by decide) (by decide) (by decide))) havol,?_,
    ((Dense.Outside.of_memory l fa.memory).trans ob).trans ot⟩
  refine ⟨ft.inputHead.trans (fb.inputHead.trans fa.inputHead),
    ft.randomCursor.trans (fb.randomCursor.trans fa.randomCursor),ft.output.trans (fb.output.trans fa.output),?_⟩
  intro j hj hn
  have hnpass : j∉Scatter.passWork := fun h => hn (Finset.mem_union_left _ h)
  have hn328 : j≠328 := fun h => by subst j; exact hn (by simp [work])
  have hn329 : j≠329 := fun h => by subst j; exact hn (by simp [work])
  have hn37 : j≠37 := fun h => by subst j; exact hnpass (by decide)
  have hn277 : j≠277 := fun h => by subst j; exact hnpass (by decide)
  have hn322 : j≠322 := fun h => by subst j; exact hnpass (by decide)
  exact (ft.tapes j hj hnpass).trans (keepb j hj hn37 hn277 hn322 hn328 hn329)

/-- Initialization is linear in physical volume and scattering is linear in
record count; the two sizes are added, never multiplied. -/
theorem costBound_polynomial (cells n B : ℕ) (points : List Scatter.Point) :
    costBound cells n B points ≤
      (Scatter.costConstant points+103000)*(cells+n+1)*(B+Scatter.costConstant points)^2 := by
  have hinit := DenseInit.costBound_polynomial cells B
  have hscatter := Scatter.costBound_polynomial n B points
  have hc : 2≤Scatter.costConstant points := by dsimp [Scatter.costConstant]; omega
  have hsq : (B+2)^2≤(B+Scatter.costConstant points)^2 := Nat.pow_le_pow_left (by omega) 2
  have hinit' := hinit.trans (Nat.mul_le_mul_left (82000*(cells+1)) hsq)
  have hvol := Nat.mul_le_mul_left 21000 hsq
  dsimp only [costBound]
  nlinarith [Nat.zero_le (cells*(B+Scatter.costConstant points)^2),Nat.zero_le (n*(B+Scatter.costConstant points)^2)]

end Maxwell.Cost.PhysicalMaterial.Preprocess
