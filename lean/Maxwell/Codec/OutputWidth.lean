import Maxwell.Codec.Output

namespace Maxwell.Codec

theorem RepresentsOutput.mono {n a b : ℕ} {x : Fin n→ℚ} {bits : List Bool}
    (h : RepresentsOutput a x bits) (hab : a≤b) : RepresentsOutput b x bits := by
  obtain ⟨pairs,hbits,hvalue,hshort⟩ := h
  exact ⟨pairs,hbits,hvalue,fun i => ⟨(hshort i).1.trans hab,(hshort i).2.trans hab⟩⟩

end Maxwell.Codec
