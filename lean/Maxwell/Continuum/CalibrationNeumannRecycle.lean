import Maxwell.Continuum.CalibrationNeumannSwap

/-! Fixed descriptor recycling retains the permanent zero pair and advances both live arrays. -/
namespace Maxwell.Continuum.Calibration.NeumannMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix Maxwell.Cost.CalibrationMatrix.Horner
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def recycleData {n : ℕ} (d : Horner.Data n) : Horner.Data n :=
  (((d.permute (Equiv.swap 0 6)).permute (Equiv.swap 1 7)).permute (Equiv.swap 10 8)).permute (Equiv.swap 11 9)

def recycleWords {n : ℕ} (words : Fin 12→Vector (List Bool) n) : Fin 12→Vector (List Bool) n :=
  fun i => words (Equiv.swap 0 6 (Equiv.swap 1 7 (Equiv.swap 10 8 (Equiv.swap 11 9 i))))

theorem recycle_sized {n B : ℕ} {d : Horner.Data n} (h : d.Sized B) : (recycleData d).Sized B :=
  Data.Sized.permute (Data.Sized.permute (Data.Sized.permute (Data.Sized.permute h _) _) _) _

def recycleCode : Code := .seq (swapCode 0 6) (.seq (swapCode 1 7)
  (.seq (swapCode 10 8) (.seq (swapCode 11 9) (.seq (selectInputCode 10 11) (selectOutputCode 5 4)))))

theorem recycle {n : ℕ} (d : Horner.Data n) (words : Fin 12→Vector (List Bool) n)
    (B : ℕ) (hsized : d.Sized B) (input : List Bool) (tape : ℕ→Bool) (count : List Bool)
    (s : Store) (hw : WorkReady count B s.val) (hd : Stored d words s.val) (hp : Ports d 4 5 8 9 s.val) :
    ∃ cost t, cost≤228*B+216 ∧ Executes input tape recycleCode cost s t ∧
      WorkReady count B t.val ∧ Stored (recycleData d) (recycleWords words) t.val ∧
      Ports (recycleData d) 10 11 5 4 t.val ∧ t.val.tapes 140=s.val.tapes 140 ∧
      t.val.memory=s.val.memory := by
  obtain ⟨c1,a,hc1,ea,haW,haD,ka,ma⟩ := swapRuntime d words 0 6 (by decide)
    B hsized input tape count s hw hd
  obtain ⟨c2,b,hc2,eb,hbW,hbD,kb,mb⟩ := swapRuntime _ _ 1 7 (by decide)
    B (Data.Sized.permute hsized _) input tape count a haW haD
  obtain ⟨c3,c,hc3,ec,hcW,hcD,kc,mc⟩ := swapRuntime _ _ 10 8 (by decide)
    B (Data.Sized.permute (Data.Sized.permute hsized _) _) input tape count b hbW hbD
  obtain ⟨c4,e,hc4,ee,heW,heD,ke,me⟩ := swapRuntime _ _ 11 9 (by decide)
    B (Data.Sized.permute (Data.Sized.permute (Data.Sized.permute hsized _) _) _) input tape count c hcW hcD
  have keep (i : ℕ) (hi : i=112∨i=113∨i=114∨i=115∨i=140) : e.val.tapes i=s.val.tapes i :=
    (ke i hi).trans ((kc i hi).trans ((kb i hi).trans (ka i hi)))
  have heP : Ports (recycleData d) 4 5 10 11 e.val := by
    refine ⟨?_,?_,?_,?_⟩
    · simpa [recycleData,Data.permute,Equiv.swap_apply_def] using
        BankArray.word_of_eq (keep 112 (by omega)) hp.inputPositive
    · simpa [recycleData,Data.permute,Equiv.swap_apply_def] using
        BankArray.word_of_eq (keep 113 (by omega)) hp.inputNegative
    · simpa [recycleData,Data.permute,Equiv.swap_apply_def] using
        BankArray.word_of_eq (keep 114 (by omega)) hp.outputPositive
    · simpa [recycleData,Data.permute,Equiv.swap_apply_def] using
        BankArray.word_of_eq (keep 115 (by omega)) hp.outputNegative
  obtain ⟨c5,f,hc5,ef,hfW,hfD,hfP,hf140,mf,_⟩ := select_input (recycleData d) (recycleWords words)
    4 5 10 11 10 11 B (recycle_sized hsized) input tape count e heW heD heP
  obtain ⟨c6,t,hc6,et,htW,htD,htP,ht140,mt,_⟩ := select_output (recycleData d) (recycleWords words)
    10 11 10 11 5 4 B (recycle_sized hsized) input tape count f hfW hfD hfP
  exact ⟨c1+(c2+(c3+(c4+(c5+c6)))),t,by omega,ea.seq (eb.seq (ec.seq (ee.seq (ef.seq et)))),
    htW,htD,htP,ht140.trans (hf140.trans (keep 140 (by omega))),
    mt.trans (mf.trans (me.trans (mc.trans (mb.trans ma))))⟩

#print axioms recycle

end Maxwell.Continuum.Calibration.NeumannMachine
