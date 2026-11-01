import Maxwell.Continuum.RationalDataflowNaturalChannels

/-! A fixed list of runtime natural-word imports into rational positive
channels. The width invariant is uniform across the list, and all source
metadata below tape 1000 is preserved. -/
namespace Maxwell.Continuum.RationalDataflow.NaturalChannel.Load
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000

abbrev Assignment := ℕ×ℕ

def code : List Assignment→Code
  | [] => .skip
  | (source,target)::rest => .seq (NaturalChannel.code .positive source target) (code rest)

def values : List Assignment→(ℕ→ℕ)→(ℕ→Parts)→(ℕ→Parts)
  | [],_,v => v
  | (source,target)::rest,n,v => values rest n (Function.update v target (replace .positive (v target) (n source)))

def Valid (S : Finset ℕ) (assignments : List Assignment) : Prop :=
  ∀a∈assignments,a.1<1000 ∧ a.2∈S

theorem positive_width (x : Parts) (n B : ℕ) (hx : x.Width B) (hn : n.bits.length ≤ B) :
    (replace .positive x n).Width B := ⟨hn,hx.2.1,hx.2.2⟩

theorem values_preserves (assignments : List Assignment) (n : ℕ→ℕ) (v : ℕ→Parts)
    (i : ℕ) (hi : ∀a∈assignments,i ≠ a.2) : values assignments n v i=v i := by
  induction assignments generalizing v with
  | nil => rfl
  | cons a rest ih =>
    rcases a with ⟨source,target⟩
    rw [values,ih _ (fun a ha=>hi a (by simp [ha]))]
    exact Function.update_of_ne (hi (source,target) (by simp)) _ _

theorem executes (S : Finset ℕ) (assignments : List Assignment) (hv : Valid S assignments)
    (n : ℕ→ℕ) (v : ℕ→Parts) (B : ℕ)
    (hw : WidthBank S B v) (hg : Good S v)
    (hn : ∀a∈assignments,(n a.1).bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hr : Ready S v s)
    (words : ∀a∈assignments,Word s.val a.1 (n a.1)) :
    ∃cost t,Executes input tape (code assignments) cost s t ∧
      cost ≤ assignments.length*(37*B+39)+1 ∧ Ready S (values assignments n v) t ∧
      WidthBank S B (values assignments n v) ∧ Good S (values assignments n v) ∧
      BinaryPrecision.Frame (ids S) s.val t.val := by
  induction assignments generalizing v s with
  | nil => exact ⟨1,s,.skip s,by simp,hr,hw,hg,BinaryPrecision.Frame.refl _ _⟩
  | cons a rest ih =>
    rcases a with ⟨source,target⟩
    obtain ⟨hs,ht⟩ := hv (source,target) (by simp)
    have hp := positivePort_ge target
    obtain ⟨c0,u,e0,hc0,r0,f0⟩ := NaturalChannel.executes S .positive source target ht (by
      change source ≠ positivePort target;omega) v (n source).bits input tape s hr
      (words (source,target) (by simp))
    simp only [addressValue_bits] at r0
    let w := Function.update v target (replace .positive (v target) (n source))
    have wwidth : WidthBank S B w := by
      intro k hk
      by_cases he : k=target
      · subst k
        simpa only [w,Function.update_self] using positive_width (v target) (n source) B (hw target ht) (hn (source,target) (by simp))
      · simpa only [w,Function.update_of_ne he] using hw k hk
    have wgood : Good S w := by
      intro k hk
      by_cases he : k=target
      · subst k
        simpa only [w,Function.update_self,replace,Parts.Valid] using hg target ht
      · simpa only [w,Function.update_of_ne he] using hg k hk
    have restWords : ∀a∈rest,Word u.val a.1 (n a.1) := by
      intro a ha
      apply word_of_eq (f0.tapes a.1 _)
      · exact words a (by simp [ha])
      · simp only [Finset.mem_singleton,port]
        have := (hv a (by simp [ha])).1
        omega
    obtain ⟨c1,t,e1,hc1,r1,w1,g1,f1⟩ := ih (fun a ha=>hv a (by simp [ha])) w wwidth wgood
      (fun a ha=>hn a (by simp [ha])) u r0 restWords
    have old := (hw target ht).1
    have incoming := hn (source,target) (by simp)
    simp only [port,dataValues_positive] at hc0
    refine ⟨c0+c1,t,e0.seq e1,?_,r1,w1,g1,(f0.mono ?_).trans f1⟩
    · simp only [List.length_cons]
      nlinarith
    · intro k hk
      simp only [Finset.mem_singleton] at hk
      subst k
      exact port_mem .positive S target ht

#print axioms executes
end Maxwell.Continuum.RationalDataflow.NaturalChannel.Load
