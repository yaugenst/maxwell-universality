import Maxwell.Continuum.SourceRoutingTreeRootCost

namespace Maxwell.Cost.RoutingPorts.Complete.Tree
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option exponentiation.threshold 1024

theorem Allocation.cost_polynomial (v : ℕ→ℕ) (B : ℕ) :
    Allocation.cost v B ≤ 2^50*(Allocation.length v+1)*(B+2)^2 := by
  have h1 : B+2 ≤ (B+2)^2 := le_self_pow₀ (by omega) (by decide : (2 : ℕ)≠0)
  have h2 : (4*(B+1)+2)^2 ≤ 16*(B+2)^2 := by nlinarith
  have h3 : (16*(B+1)+2)^2 ≤ 256*(B+2)^2 := by nlinarith
  have h4 := Nat.mul_le_mul_left (2^31*(Allocation.length v+1)) h3
  have h5 : (B+2)^2 ≤ (Allocation.length v+1)*(B+2)^2 := Nat.le_mul_of_pos_left _ (by omega)
  dsimp only [Allocation.cost]
  nlinarith only [h1,h2,h3,h4,h5]

theorem runWidth_depth (heap rows total : ℕ) : total+1 ≤ runWidth heap rows total := by
  have h:=ControllerWidth.population_width heap (2^(total+rows)) (total+rows+1) total total le_rfl
  simpa only [Nat.size_eq_bits_len,Nat.size_pow,runWidth] using h

theorem runWidth_word (heap rows total : ℕ) : total+rows+1 ≤ runWidth heap rows total := by
  have h : (2 : ℕ)^(total+rows) ≤
      ControllerWidth.ceiling heap (2^(total+rows)) (total+rows+1) total := by
    dsimp only [ControllerWidth.ceiling]
    exact (((Nat.le_add_left _ _).trans (Nat.le_add_right _ _)).trans
      (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
  have hbits:=Maxwell.Continuum.RationalWords.bits_mono h
  simpa only [Nat.size_eq_bits_len,Nat.size_pow,runWidth,ControllerWidth.baseWidth] using hbits

theorem TreeStartup.cost_polynomial (total forward backward : ℕ)
    (hf : forward ≤ TreeStartup.heap total backward) :
    TreeStartup.cost total forward backward ≤ 2^200*runVolume (TreeStartup.heap total backward) total total := by
  let heap:=TreeStartup.heap total backward
  let L:=runWidth heap total total
  let q:=(2 : ℕ)^total
  let n:=(2 : ℕ)^(total+total)
  have seed:=TreeStartup.bits_bounded total forward backward hf
  change TreeStartup.bits total forward backward ≤ 4*L+4 at seed
  have stage : TreeStartup.stageBits total forward backward+2 ≤ 2^22*(L+2) := by
    dsimp only [TreeStartup.stageBits]
    omega
  have square : (TreeStartup.stageBits total forward backward+2)^2 ≤ 2^44*(L+2)^2 := by
    calc
      _ ≤ (2^22*(L+2))^2 := Nat.pow_le_pow_left stage 2
      _ = _ := by ring
  have initialSquare : (TreeStartup.bits total forward backward+2)^2 ≤ 16*(L+2)^2 := by
    calc
      _ ≤ (4*(L+2))^2 := Nat.pow_le_pow_left (by omega) 2
      _ = _ := by ring
  have word : total+total+1 ≤ L := runWidth_word heap total total
  have depth : total+1 ≤ L := runWidth_depth heap total total
  have allocation : Allocation.length (TreeStartup.powered total forward backward)+1 ≤
      23*(q+1)*(n+1)*(L+2) := by
    rw [TreeStartup.allocation_length]
    have hp : 2^(total+1)-1 ≤ 2*q := by dsimp only [q];rw [pow_succ'];omega
    have hs : TreeStartup.wordWidth total ≤ L := word
    have h := Nat.mul_le_mul hp (Nat.mul_le_mul_left (11*n) hs)
    dsimp only [TreeStartup.wordWidth] at h
    have product : q*n*L ≤ (q+1)*(n+1)*(L+2) := by gcongr <;> omega
    have positive : 1 ≤ (q+1)*(n+1)*(L+2) := Nat.succ_le_of_lt (by positivity)
    dsimp only [stride,TreeStartup.count] at h ⊢
    change (2^(total+1)-1)*(11*(n*(total+total+1)))+1 ≤ _
    nlinarith only [h,product,positive]
  have alloc0:=Allocation.cost_polynomial (TreeStartup.powered total forward backward)
    (TreeStartup.stageBits total forward backward)
  have alloc : Allocation.cost (TreeStartup.powered total forward backward)
      (TreeStartup.stageBits total forward backward) ≤
      2^100*runVolume heap total total := by
    calc
      _ ≤ 2^50*(23*(q+1)*(n+1)*(L+2))*(2^44*(L+2)^2) :=
        alloc0.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ allocation) square)
      _ = (2^50*23*2^44)*runVolume heap total total := by dsimp only [runVolume,q,n,L];ring
      _ ≤ 2^100*runVolume heap total total := Nat.mul_le_mul_right _ (by norm_num)
  have M1:=runVolume_one heap total total
  have M3:=runVolume_width heap total total
  have smallPower : (L+2)^2 ≤ (L+2)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have bits : total.bits.length ≤ L := (natural_bits_length_le total).trans (by omega)
  have powerCost : (total+1)*(13*total.bits.length+25)+21*total.bits.length+27 ≤
      100*(L+2)^2 := by nlinarith only [depth,bits]
  dsimp only [TreeStartup.cost]
  change _ ≤ 2^200*runVolume heap total total
  nlinarith only [initialSquare,square,alloc,M1,M3,smallPower,powerCost]

theorem CompleteTree.cost_polynomial (total forward backward : ℕ)
    (hf : forward ≤ TreeStartup.heap total backward) :
    CompleteTree.cost total forward backward ≤
      2^700*(2^total+1)^3*(runWidth (TreeStartup.heap total backward) total total+2)^4 := by
  let heap:=TreeStartup.heap total backward
  let q:=(2 : ℕ)^total
  let L:=runWidth heap total total
  have first:=TreeStartup.cost_polynomial total forward backward hf
  have last:=RootRun.cost_polynomial heap total total
  have hd:=runWidth_depth heap total total
  have count : (2 : ℕ)^(total+total)=q^2 := by dsimp only [q];rw [pow_two,pow_add]
  have bound : runVolume heap total total ≤ (q+1)^3*(L+2)^3 := by
    dsimp only [runVolume]
    rw [count]
    change (q+1)*(q^2+1)*(L+2)^3 ≤ (q+1)^3*(L+2)^3
    gcongr
    nlinarith
  have hl : (total+1)*runVolume heap total total ≤ (q+1)^3*(L+2)^4 := by
    calc
      _ ≤ (L+2)*((q+1)^3*(L+2)^3) := Nat.mul_le_mul (by omega) bound
      _ = _ := by ring
  have hf' : runVolume heap total total ≤ (q+1)^3*(L+2)^4 :=
    (Nat.le_mul_of_pos_left _ (by omega : 0<total+1)).trans hl
  dsimp only [CompleteTree.cost]
  change _ ≤ 2^700*(q+1)^3*(L+2)^4
  nlinarith only [first,last,hl,hf']

#print axioms CompleteTree.cost_polynomial
end Maxwell.Cost.RoutingPorts.Complete.Tree
