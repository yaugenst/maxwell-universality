import Maxwell.Cost.PhysicalMaterial.ScatterPass

namespace Maxwell.Cost.PhysicalMaterial.Scatter
open Structured RationalAccumulator
set_option maxHeartbeats 2000000

def code (points : List Point) : Code := .seq (.call (WordTransfer.clone 304 303)) (scanCode points)
def costBound (n B : ℕ) (points : List Point) : ℕ := 15*B+17+scanBudget n B points

/-- The descriptor count is read from tape304; no host iteration or host
material lookup occurs in this fixed finite program. -/
theorem executes {n cells : ℕ} (d : Descriptors.Data n) (l : Dense.Layout cells)
    (points : List Point) (locations : Fin n → Point → Fin cells)
    (nums dens : Vector (List Bool) cells) (ny nz B : ℕ)
    (hd : d.Sized B) (hl : l.Sized B) (hwidth : d.width = l.width)
    (hsep : SeparatedData d l) (hn : n < 2^B) (hcells : cells < 2^B)
    (hindex : ∀ i p, p ∈ points → flatIndex (anchor d i) p ny nz = (locations i p).val)
    (hroom : ∀ i p, p ∈ points → ∀ j, 0 ≤ (anchor d i j : ℤ)+p j)
    (hnyB : ny.bits.length ≤ B) (hnzB : nz.bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : PointReady s.val) (hdata : Descriptors.Stored d s.val)
    (hdense : Dense.Stored l nums dens s.val)
    (h302 : Blank s.val 302) (h303 : Blank s.val 303) (hcount : Word s.val 304 n)
    (hbank : Descriptors.Bank s.val (fun _ => 0)) (hny : Word s.val 251 ny) (hnz : Word s.val 252 nz) :
    ∃ cost t, cost ≤ costBound n B points ∧ Executes input tape (code points) cost s t ∧
      PointReady t.val ∧ Descriptors.Stored d t.val ∧ Descriptors.Bank t.val (fun _ => 0) ∧
      Dense.Stored l (filledNums d l points locations nums n) (filledDens d l points locations dens n) t.val ∧
      Blank t.val 302 ∧ Blank t.val 303 ∧ PassFrame s.val t.val ∧ Dense.Outside l s.val t.val := by
  have hnlen : n.bits.length ≤ B := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hn
  obtain ⟨countOrigin,hcountWord⟩ := hcount
  obtain ⟨counterOrigin,hcounterBlank⟩ := h303
  obtain ⟨a,ea,hat,fa⟩ := WordCall.clone 304 303 (by decide) input tape n.bits countOrigin counterOrigin
    s hcountWord hcounterBlank
  have keep (j : ℕ) (hj : j ≠ 303) : a.val.tapes j = s.val.tapes j := by simp [hat,hj]
  have har : PointReady a.val :=
    ⟨(fun j hj => blank_of_eq (keep j (by omega)) (hs.1 j hj)),
      blank_of_eq (keep 37 (by decide)) hs.2.1,
      blank_of_eq (keep 292 (by decide)) hs.2.2.1,
      blank_of_eq (keep 322 (by decide)) hs.2.2.2.1,
      fun j => blank_of_eq (keep (324+j.val) (by omega)) (hs.2.2.2.2 j)⟩
  have had : Descriptors.Stored d a.val := by
    refine ⟨BankArray.word_of_eq (keep 300 (by decide)) hdata.width,
      BankArray.word_of_eq (keep 301 (by decide)) hdata.clock,?_,?_⟩
    · intro j
      exact BankArray.word_of_eq (keep (Descriptors.baseTape j) (by simp only [Descriptors.baseTape]; omega)) (hdata.bases j)
    · intro j
      simpa only [fa.2.2.1] using hdata.arrays j
  have hal : Dense.Stored l nums dens a.val :=
    ⟨BankArray.word_of_eq (keep 300 (by decide)) hdense.width,
      BankArray.word_of_eq (keep 301 (by decide)) hdense.clock,
      BankArray.word_of_eq (keep 320 (by decide)) hdense.numBase,
      BankArray.word_of_eq (keep 321 (by decide)) hdense.denBase,
      by simpa only [fa.2.2.1] using hdense.nums,by simpa only [fa.2.2.1] using hdense.dens⟩
  have habank : Descriptors.Bank a.val (fun _ => 0) := fun j =>
    word_of_eq (keep (Descriptors.targetTape j) (by have := Descriptors.targetTape_bounds j; omega)) (hbank j)
  have hai : BankArray.Word a.val 302 [] := by
    obtain ⟨origin,ho⟩ := h302
    exact ⟨origin,by simpa using (keep 302 (by decide)).trans ho⟩
  obtain ⟨sc,t,hsc,es,htr,htd,htb,htl,ht302,ht303,ft,ot⟩ := scan d l points locations nums dens ny nz B
    hd hl hwidth hsep hn hcells hindex hroom hnyB hnzB input tape [] n.bits rfl (by simp)
    (by simp) hnlen counterOrigin a har had hal hai (by simp [hat]) habank
    (word_of_eq (keep 251 (by decide)) hny) (word_of_eq (keep 252 (by decide)) hnz)
  have frame : PassFrame s.val a.val :=
    ⟨fa.2.1,fa.2.2.2.1,fa.2.2.2.2.1,fun j _ hj => keep j (by
      intro he; subst j; exact hj (by simp [passWork]))⟩
  exact ⟨15*n.bits.length+17+sc,t,by dsimp only [costBound]; omega,ea.seq es,
    htr,htd,htb,htl,ht302,ht303,frame.trans ft,(Dense.Outside.of_memory l fa.2.2.1).trans ot⟩

def costConstant (points : List Point) : ℕ := constant points+102000

/-- Linear descriptor dependence, with only a fixed-prototype constant and a
quadratic binary-width factor. -/
theorem costBound_polynomial (n B : ℕ) (points : List Point) :
    costBound n B points ≤ costConstant points*(n+1)*(B+costConstant points)^2 := by
  let C := costConstant points
  have hc : 102000 ≤ C := by dsimp [C,costConstant]; omega
  have hcp : constant points ≤ C := by dsimp [C,costConstant]; omega
  have hsmall : (B+2)^2 ≤ (B+C)^2 := Nat.pow_le_pow_left (by omega) 2
  have hlist := (listBudget_le points B).trans
    (Nat.mul_le_mul_left (constant points) (Nat.pow_le_pow_left (by omega) 2 : (B+constant points)^2 ≤ (B+C)^2))
  have hrec : recordBudget points B ≤ (101000+constant points)*(B+C)^2 := by
    dsimp only [recordBudget]
    nlinarith [Nat.mul_le_mul_left 101000 hsmall]
  have hlin : 40*B+40 ≤ 1000*(B+C)^2 := by nlinarith
  have hnrec := Nat.mul_le_mul_left n hrec
  have hnlin := Nat.mul_le_mul_left (n+1) hlin
  dsimp only [costBound,scanBudget]
  change 15*B+17+((n+1)*(13*B+15)+n*recordBudget points B+12*B+8) ≤ C*(n+1)*(B+C)^2
  dsimp only [C,costConstant] at *
  nlinarith [Nat.zero_le ((B+constant points+102000)^2)]

end Maxwell.Cost.PhysicalMaterial.Scatter
