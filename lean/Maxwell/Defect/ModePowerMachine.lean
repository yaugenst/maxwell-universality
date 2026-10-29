import Maxwell.Defect.ModePowerInteger
import Maxwell.Cost.CalibrationMatrix.PowerSemantics

namespace Maxwell.Defect
open Cost Cost.Structured Cost.CalibrationMatrix
open RationalAccumulator (Blank)
variable {n : ℕ}

@[simp] theorem matrixPower_eq_channelPower (A : ChannelMatrix n) (x : Channels n) (N : ℕ) :
    matrixPower A x N = channelPower A x N := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [matrixPower, channelPower, ih]

/-- The already bounded integer mode powers execute on the actual finite
BitRAM, including every indexed read, signed product, write and counter.
The linear-in-degree word bound discharges all intermediate write fits. -/
theorem channelPower_compiled_run (b : Buffers n) (A : ChannelMatrix n) (x : Channels n)
    (hdecode : b.data.Decodes A x) (N B a v : ℕ) (hA : A.Bounded a) (hx : x.Bounded v)
    (hwidth : v.size+(2*n*a).size*N ≤ addressValue b.data.width)
    (hsized : b.Sized B) (hsep : b.Separated)
    (hm : n*n < 2^B) (hn : n < 2^B) (hW : 0 < addressValue b.data.width)
    (input : List Bool) (tape : ℕ → Bool) (count outer : List Bool)
    (hcount : addressValue count = n) (hcl : count.length ≤ B)
    (houter : addressValue outer = N) (hol : outer.length ≤ B)
    (origin : ℤ) (s : Store) (hs : b.Ready count B s.val)
    (h140 : s.val.tapes 140 = BitTape.shifted outer origin) :
    ∃ t : Store,
      (runPriced (powerCode.compile.next input tape) (powerCost N n B+1) s.val).finished =
        some (t.place powerCode.size) ∧
      (runPriced (powerCode.compile.next input tape) (powerCost N n B+1) s.val).instructions ≤
        630000*(N+1)*(n+1)^2*(B+2)^2 ∧
      (b.iterate N).Ready count B t.val ∧ (b.iterate N).data.Decodes A (channelPower A x N) ∧
      Blank t.val 140 ∧ PowerFrame s.val t.val ∧ b.Outside s.val t.val := by
  have hb (k : ℕ) (hk : k ≤ N) (i : Fin n) := channelPower_bit_bound A x a v hA hx k i
  have hp : ∀ k, k ≤ N → ∀ i,
      ((matrixPower A x k).positive i).bits.length ≤ addressValue b.data.width := by
    intro k hk i
    rw [Nat.size_eq_bits_len, matrixPower_eq_channelPower]
    exact (hb k hk i).1.trans ((by gcongr : v.size+(2*n*a).size*k ≤ v.size+(2*n*a).size*N).trans hwidth)
  have hneg : ∀ k, k ≤ N → ∀ i,
      ((matrixPower A x k).negative i).bits.length ≤ addressValue b.data.width := by
    intro k hk i
    rw [Nat.size_eq_bits_len, matrixPower_eq_channelPower]
    exact (hb k hk i).2.trans ((by gcongr : v.size+(2*n*a).size*k ≤ v.size+(2*n*a).size*N).trans hwidth)
  simpa only [matrixPower_eq_channelPower] using power_channels b A x hdecode N B hsized hsep hp hneg
    hm hn hW input tape count outer hcount hcl houter hol origin s hs h140

end Maxwell.Defect
