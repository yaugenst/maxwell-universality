import Maxwell.Continuum.RationalDataflowArrayOutput
import Maxwell.Cost.ArraySnapshot

/-! An output table starts from arbitrary existing memory. All descriptor
words remain actual machine data; the snapshot imposes no initialization. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator

def Table.snapshot (n : ℕ) (memory : ℕ→Bool)
    (width positive negative denominator clock : List Bool)
    (hwidth : 0<width.length) (hclock : clock.length=addressValue width) : Table n :=
  ⟨width,positive,negative,denominator,clock,
    BitArray.snapshot memory (addressValue positive) (addressValue width) n,
    BitArray.snapshot memory (addressValue negative) (addressValue width) n,
    BitArray.snapshot memory (addressValue denominator) (addressValue width) n,hwidth,hclock⟩

theorem Table.snapshot_outputReady (n : ℕ) (s : Store)
    (width positive negative denominator clock : List Bool)
    (hwidth : 0<width.length) (hclock : clock.length=addressValue width)
    (scratch : BankArray.Scratch s.val) (seven : Blank s.val 7) (packing : Blank s.val 37)
    (w : BankArray.Word s.val 210 width) (p : BankArray.Word s.val 212 positive)
    (m : BankArray.Word s.val 213 negative) (d : BankArray.Word s.val 214 denominator)
    (c : BankArray.Word s.val 215 clock) :
    (Table.snapshot n s.val.memory width positive negative denominator clock hwidth hclock).OutputReady s :=
  ⟨scratch,seven,packing,w,p,m,d,c,BitArray.snapshot_represents _ _ _ _,
    BitArray.snapshot_represents _ _ _ _,BitArray.snapshot_represents _ _ _ _⟩

#print axioms Table.snapshot_outputReady
end Maxwell.Continuum.RationalDataflow.PartArray
