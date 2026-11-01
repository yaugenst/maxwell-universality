import Maxwell.Continuum.ParameterOuterStageData

/-! Raw source-side operands and their physical interpretation. No values
are normalized by specification; their executed integer pairs are retained. -/
namespace Maxwell.Continuum.Parameters.OuterMachine
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048

structure Data where
  constant : ℕ
  sourceSize : ℕ
  wells : ℕ
  conditionNum : ℕ
  conditionDen : ℕ
  epsilonNum : ℕ
  epsilonDen : ℕ
  span : Fin 3→ℕ

structure Data.Positive (D : Data) : Prop where
  sourceSize : 0<D.sourceSize
  conditionNum : 0<D.conditionNum
  conditionDen : 0<D.conditionDen
  epsilonNum : 0<D.epsilonNum
  epsilonDen : 0<D.epsilonDen

def dataOf (v : ℕ→ℕ) : Data :=
  ⟨v 2210,v 2211,v 2212,v 2213,v 2214,v 2215,v 2216,fun j=>v (2217+j.val)⟩

def Data.input (D : Data) (hD : D.Positive) : Input :=
  ⟨D.sourceSize,D.wells,D.span,(D.conditionNum:ℚ)/D.conditionDen,
    (D.epsilonNum:ℚ)/D.epsilonDen,hD.sourceSize,
    div_pos (by exact_mod_cast hD.conditionNum) (by exact_mod_cast hD.conditionDen),
    div_pos (by exact_mod_cast hD.epsilonNum) (by exact_mod_cast hD.epsilonDen)⟩

def Data.spacing (D : Data) (k : ℕ) : SpacingMachine.Data :=
  ⟨D.constant,stageLength k,D.conditionNum,D.conditionDen,D.epsilonNum,D.epsilonDen⟩

def Data.detuningDen (D : Data) (hD : D.Positive) (e k : ℕ) : ℕ :=
  2^(Nat.clog 2 (OuterTau.budgetDen (stageLength k) (stageSpacing (D.input hD) e k)))

def Data.buffer (D : Data) (hD : D.Positive) (e k : ℕ) : BufferMachine.Data :=
  let d := stageSpacing (D.input hD) e k
  ⟨D.constant,stageLength k,D.wells,D.sourceSize,D.conditionNum,D.conditionDen,
    D.epsilonNum,D.epsilonDen,(stageLength k)^2,2^1026*8^d,1,D.detuningDen hD e k,
    stageSpan (D.input hD) e k⟩

theorem Data.buffer_alpha (D : Data) (hD : D.Positive) (e k : ℕ) :
    ((D.buffer hD e k).alphaNum:ℚ)/(D.buffer hD e k).alphaDen=
      alpha (stageLength k) (stageSpacing (D.input hD) e k) := by
  simp only [Data.buffer,alpha,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat,one_div,inv_pow]
  ring

theorem Data.buffer_tau (D : Data) (hD : D.Positive) (e k : ℕ) :
    ((D.buffer hD e k).tauNum:ℚ)/(D.buffer hD e k).tauDen=stageTau (D.input hD) e k := by
  simp only [Data.buffer,Data.detuningDen,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat,stageTau]
  exact (OuterTau.tau_eq _ _ (stageLength_pos k)).symm

theorem Data.selected_buffer (D : Data) (hD : D.Positive) (e k : ℕ) :
    let A := D.buffer hD e k
    selectedBuffer e A.wells A.sourceSize A.length (stageSpacing (D.input hD) e k) A.span
      ((A.conditionNum:ℚ)/A.conditionDen) ((A.epsilonNum:ℚ)/A.epsilonDen)
      ((A.tauNum:ℚ)/A.tauDen) hD.sourceSize
      (div_pos (by exact_mod_cast hD.epsilonNum) (by exact_mod_cast hD.epsilonDen))
      (by simp only [A,Data.buffer];unfold Data.detuningDen;positivity)=stageBuffer (D.input hD) e k := by
  dsimp only
  simp only [Data.buffer,Data.detuningDen,stageBuffer,stageTau,Data.input,
    OuterTau.tau_eq _ _ (stageLength_pos k),Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat]

#print axioms Data.selected_buffer
end Maxwell.Continuum.Parameters.OuterMachine
