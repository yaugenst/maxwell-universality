import Maxwell.Cost.TapeOrigins
import Maxwell.Cost.BankArray.Common

namespace Maxwell.Cost

@[simp] theorem BitTape.translate_blank (offset : ℤ):
    BitTape.blank.translate offset={BitTape.blank with head:=offset}:=by simp [translate,blank]

@[simp] theorem BitTape.translate_blankAt (origin offset : ℤ):
    (BitTape.mk origin (fun _=>none)).translate offset=BitTape.mk (origin+offset) (fun _=>none):=rfl

@[simp] theorem BitTape.translate_shifted (bits : List Bool) (origin offset : ℤ):
    (BitTape.shifted bits origin).translate offset=BitTape.shifted bits (origin+offset):=by
  unfold translate shifted
  congr 1
  funext j
  have le : origin≤j-offset ↔origin+offset≤j:=by omega
  have sub : j-offset-origin=j-(origin+offset):=by omega
  simp only [le,sub]

@[simp] theorem BitTape.translate_ofList (bits : List Bool) (offset : ℤ):
    (BitTape.ofList bits).translate offset=BitTape.shifted bits offset:=by
  rw [←BitTape.shifted_zero,BitTape.translate_shifted,zero_add]

namespace Structured
@[simp] theorem Store.translateTapes_inverse (s : Store) (offset : ℕ→ℤ):
    (s.translateTapes (fun i=>-offset i)).translateTapes offset=s:=by
  apply Subtype.ext
  exact BitRAMState.translateTapes_inverse s.val offset
end Structured

theorem BankArray.Word.translateTapes {s : BitRAMState} {bank : ℕ} {bits : List Bool}
    (word : BankArray.Word s bank bits) (offset : ℕ→ℤ):
    BankArray.Word (s.translateTapes offset) bank bits:=by
  obtain ⟨origin,stored⟩:=word
  exact ⟨origin+offset bank,by simp only [BitRAMState.translateTapes,stored,BitTape.translate_shifted]⟩

#print axioms BankArray.Word.translateTapes
end Maxwell.Cost
