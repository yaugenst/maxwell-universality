import Maxwell.Continuum.FourierTensorModeAllocationData

/-! The row allocation plan executes from stored parameters and source
descriptors. No runtime length or buffer address is supplied as an oracle. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def InputWidth (M L R P width bp bn bd W : ℕ) : Prop :=
  ∀i∈inputs,(initial M L R P width bp bn bd i).bits.length≤W
def setupChanged : Finset ℕ := {0,1,2,3,145,201,311,322,353,356,357,358,360,361,362,725,726,727}

theorem initial_width (M L R P width bp bn bd W : ℕ)
    (h : InputWidth M L R P width bp bn bd W) (i : ℕ) :
    (initial M L R P width bp bn bd i).bits.length≤W := by
  by_cases hi : i∈inputs
  · exact h i hi
  · simp only [inputs,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
    simp [initial,hi]

theorem scanned_width (M L R P width bp bn bd W : ℕ)
    (h : InputWidth M L R P width bp bn bd W) (i : ℕ) :
    (scanned M L R P width bp bn bd i).bits.length≤W := by
  have hm : M.bits.length≤W := by simpa [initial] using h 350 (by simp [inputs])
  have hl : L.bits.length≤W := by simpa [initial] using h 352 (by simp [inputs])
  have hr : R.bits.length≤W := by simpa [initial] using h 354 (by simp [inputs])
  by_cases h360 : i=360
  · subst i;simpa [scanned] using (Machin.Runtime.nat_bits_le_self _).trans hm
  by_cases h361 : i=361
  · subst i;simpa [scanned] using (Machin.Runtime.nat_bits_le_self _).trans hl
  by_cases h362 : i=362
  · subst i;simpa [scanned] using (Machin.Runtime.nat_bits_le_self _).trans hr
  simpa only [scanned,Function.update_of_ne h360,Function.update_of_ne h361,
    Function.update_of_ne h362] using initial_width M L R P width bp bn bd W h i

theorem scan_executes (M L R P width bp bn bd W : ℕ)
    (h : InputWidth M L R P width bp bn bd W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids (initial M L R P width bp bn bd) s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape scanCode cost s t ∧ cost≤2^10*(W+2)^2 ∧
      NatAssign.Bank ids (scanned M L R P width bp bn bd) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame {360,361,362} s.val t.val := by
  obtain ⟨c0,u,e0,hc0,b0,z0,f0⟩ := NatAssign.stored_length ids 350 360 (by decide)
    (by simp [ids,inputs]) (by simp [ids]) (by decide) (initial M L R P width bp bn bd)
    (by simp [initial]) input tape s hb hz
  obtain ⟨c1,v,e1,hc1,b1,z1,f1⟩ := NatAssign.stored_length ids 352 361 (by decide)
    (by simp [ids,inputs]) (by simp [ids]) (by decide) _
    (by simp [initial]) input tape u b0 z0
  obtain ⟨c2,t,e2,hc2,b2,z2,f2⟩ := NatAssign.stored_length ids 354 362 (by decide)
    (by simp [ids,inputs]) (by simp [ids]) (by decide) _
    (by simp [initial]) input tape v b1 z1
  have hm : M.bits.length≤W := by simpa [initial] using h 350 (by simp [inputs])
  have hl : L.bits.length≤W := by simpa [initial] using h 352 (by simp [inputs])
  have hr : R.bits.length≤W := by simpa [initial] using h 354 (by simp [inputs])
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,?_,z2,
    (f0.mono (by decide)).trans ((f1.mono (by decide)).trans (f2.mono (by decide)))⟩
  · simp only [initial,ite_true,ite_false,show (350:ℕ)≠200 by decide,
      show (350:ℕ)≠202 by decide,show (350:ℕ)≠203 by decide,show (350:ℕ)≠204 by decide] at hc0
    have hs0 : c0≤48*(M.bits.length+1)^2+1 := hc0
    have hs1 : c1≤48*(L.bits.length+1)^2+1 := by simpa [initial] using hc1
    have hs2 : c2≤48*(R.bits.length+1)^2+1 := by simpa [initial] using hc2
    have hp0 := Nat.pow_le_pow_left (show M.bits.length+1≤W+2 by omega) 2
    have hp1 := Nat.pow_le_pow_left (show L.bits.length+1≤W+2 by omega) 2
    have hp2 := Nat.pow_le_pow_left (show R.bits.length+1≤W+2 by omega) 2
    nlinarith only [hs0,hs1,hs2,hp0,hp1,hp2,Nat.zero_le W]
  · simpa [initial,scanned] using b2

theorem executes (M L R P width bp bn bd W : ℕ) (hW : 5≤W)
    (h : InputWidth M L R P width bp bn bd W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids (initial M L R P width bp bn bd) s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤2^116*(W+2)^2 ∧
      NatAssign.Bank ids (values M L R P width bp bn bd) t.val ∧
      (∀i∈ids,(values M L R P width bp bn bd i).bits.length≤2^32*(W+1)) ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame setupChanged s.val t.val := by
  obtain ⟨c0,u,e0,hc0,b0,z0,f0⟩ := scan_executes M L R P width bp bn bd W h input tape s hb hz
  obtain ⟨c1,t,e1,hc1,b1,z1,f1⟩ := NatAssign.executes ids ids_ge instructions instructions_valid
    (scanned M L R P width bp bn bd) input tape u b0 z0
  have hw : ∀i∈ids,(scanned M L R P width bp bn bd i).bits.length≤W :=
    fun i _ => scanned_width M L R P width bp bn bd W h i
  have hlit : ∀a∈instructions,a.literalWidth≤W := by
    simp [instructions,NatAssign.Instruction.literalWidth,
      show (2:ℕ).bits.length=2 by decide,
      show (3:ℕ).bits.length=2 by decide,show (5:ℕ).bits.length=3 by decide,
      show (16:ℕ).bits.length=5 by decide]
    omega
  have price := hc1.trans (NatAssign.price_bound ids instructions instructions_valid
    (scanned M L R P width bp bn bd) W hw hlit)
  have wb := NatAssign.values_width_bound ids instructions instructions_valid
    (scanned M L R P width bp bn bd) W hw hlit
  refine ⟨c0+c1,t,e0.seq e1,?_,b1,?_,z1,(f0.mono (by decide)).trans (f1.mono (by decide))⟩
  · have hc1' : c1≤3000*8^32*(W+2)^2 := by simpa only [instructions,List.length_cons,List.length_nil] using price
    have hcoef : 2^10+3000*8^32≤(2:ℕ)^116 := by norm_num
    calc
      _ ≤ (2^10+3000*8^32)*(W+2)^2 := by nlinarith only [hc0,hc1']
      _ ≤ _ := Nat.mul_le_mul_right _ hcoef
  · intro i hi
    have hh := wb i hi
    change (values M L R P width bp bn bd i).bits.length+1≤2^32*(W+1) at hh
    omega

#print axioms executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
