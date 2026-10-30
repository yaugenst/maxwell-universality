import Maxwell.Continuum.SourceRoutingSortNeighbors

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Maxwell.Logical.Routing GeometrySort
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def exchanges {q : ℕ} (round : ℕ) (saved : SortArrays.Keys q) (p : Port q) : Prop :=
  if 0<maximumFlag round p then SortArrays.keyAt saved p<SortArrays.keyAt saved (neighborPort round p)
  else SortArrays.keyAt saved (neighborPort round p)<SortArrays.keyAt saved p

instance {q : ℕ} (round : ℕ) (saved : SortArrays.Keys q) (p : Port q) : Decidable (exchanges round saved p) :=
  by unfold exchanges;infer_instance

def lower {q : ℕ} (round : ℕ) (p : Port q) : ℕ :=
  if 0<maximumFlag round p then p.1.val-1 else p.1.val

def movement {q : ℕ} (round : ℕ) (saved : SortArrays.Keys q) (p : Port q) : RowLayer.Move :=
  if exchanges round saved p then .exchange (lower round p) (decide (maximumFlag round p=0)) else .idle

theorem active_left {q : ℕ} (round : ℕ) (saved : SortArrays.Keys q) (p : Port q) :
    (SortArrays.arraySelection round saved).active p.1.val p.2.val=true ↔
      left round p ∧ SortArrays.word saved p.2.val (p.1.val+1)<SortArrays.keyAt saved p := by
  simp only [SortArrays.arraySelection,decide_eq_true_eq,left,SortArrays.word_at]
  have row:=p.2.isLt
  tauto

theorem active_previous {q : ℕ} (round : ℕ) (saved : SortArrays.Keys q) (p : Port q) :
    (0<p.1.val ∧ (SortArrays.arraySelection round saved).active (p.1.val-1) p.2.val=true) ↔
      right round p ∧ SortArrays.keyAt saved p<SortArrays.word saved p.2.val (p.1.val-1) := by
  simp only [SortArrays.arraySelection,decide_eq_true_eq,right]
  constructor
  · rintro ⟨positive,room,parity,_,order⟩
    have same : p.1.val-1+1=p.1.val := by omega
    rw [same] at parity order
    exact ⟨⟨positive,parity⟩,by simpa only [SortArrays.word_at] using order⟩
  · rintro ⟨⟨positive,parity⟩,order⟩
    have same : p.1.val-1+1=p.1.val := by omega
    exact ⟨positive,by simpa only [same] using p.1.isLt,by simpa only [same] using parity,p.2.isLt,
      by simpa only [same,SortArrays.word_at] using order⟩

theorem movement_eq {q : ℕ} (round : ℕ) (saved : SortArrays.Keys q) (p : Port q) :
    movement round saved p=RowLayer.movement (SortArrays.arraySelection round saved) p := by
  have notBoth : ¬(left round p ∧ right round p) := by dsimp only [left,right];omega
  unfold RowLayer.movement
  simp only [active_left,active_previous]
  by_cases hl : left round p
  · have hr : ¬right round p := fun h => notBoth ⟨hl,h⟩
    have neighborWord : SortArrays.keyAt saved (neighborPort round p)=SortArrays.word saved p.2.val (p.1.val+1) := by
      simp [neighborPort,hl,SortArrays.word,p.2.isLt,hl.1]
    simp only [movement,exchanges,lower,maximumFlag,hl,hr,ite_true,ite_false,
      show ¬(0 : ℕ)<0 by decide,decide_true,neighborWord,true_and,false_and]
  · by_cases hr : right round p
    · have neighborWord : SortArrays.keyAt saved (neighborPort round p)=SortArrays.word saved p.2.val (p.1.val-1) := by
        have room : p.1.val-1<q := (Nat.sub_le _ _).trans_lt p.1.isLt
        simp [neighborPort,hl,hr,SortArrays.word,p.2.isLt,room]
      simp only [movement,exchanges,lower,maximumFlag,hl,hr,ite_true,ite_false,
        show (0 : ℕ)<1 by decide,show ¬(1 : ℕ)=0 by decide,decide_false,neighborWord,true_and,false_and]
    · simp [movement,exchanges,maximumFlag,neighborPort,hl,hr]

theorem destination_eq {q : ℕ} (round : ℕ) (saved : SortArrays.Keys q) (p : Port q) :
    RowLayer.destination (SortArrays.arraySelection round saved) p=
      if exchanges round saved p then neighborPort round p else p := by
  apply Prod.ext
  · apply Fin.ext
    simp only [RowLayer.destination,RowLayer.destinationColumn,←movement_eq,movement]
    by_cases exchange : exchanges round saved p
    · have hleftRight : left round p ∨ right round p := by
        by_contra h
        push Not at h
        simp [exchanges,maximumFlag,neighborPort,h.1,h.2] at exchange
      rcases hleftRight with hl|hr
      · simp [exchange,lower,maximumFlag,neighborPort,hl]
      · have hl : ¬left round p := by dsimp only [left,right] at *;omega
        simp [exchange,lower,maximumFlag,neighborPort,hl,hr]
    · simp [exchange]
  · by_cases h : exchanges round saved p
    · simp only [h,ite_true,RowLayer.destination]
      unfold neighborPort
      split_ifs <;> rfl
    · simp only [h,ite_false,RowLayer.destination]

#print axioms movement_eq
#print axioms destination_eq
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
