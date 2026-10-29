import Maxwell.Certificate.GlobalSymbol
namespace Maxwell.Certificate.GlobalWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def roots : Fin 20 → DyadicRectangle := ![⟨4503599627370496, 0, 16⟩, ⟨4283177772395120, 1391688820718160, 16⟩, ⟨3643488634403408, 2647149443198240, 16⟩, ⟨2647149443198240, 3643488634403408, 16⟩, ⟨1391688820718160, 4283177772395120, 16⟩, ⟨0, 4503599627370496, 16⟩, ⟨-1391688820718176, 4283177772395120, 16⟩, ⟨-2647149443198256, 3643488634403408, 16⟩, ⟨-3643488634403424, 2647149443198240, 16⟩, ⟨-4283177772395136, 1391688820718160, 16⟩, ⟨-4503599627370496, 0, 16⟩, ⟨-4283177772395136, -1391688820718176, 16⟩, ⟨-3643488634403424, -2647149443198256, 16⟩, ⟨-2647149443198256, -3643488634403424, 16⟩, ⟨-1391688820718176, -4283177772395136, 16⟩, ⟨0, -4503599627370496, 16⟩, ⟨1391688820718160, -4283177772395136, 16⟩, ⟨2647149443198240, -3643488634403424, 16⟩, ⟨3643488634403408, -2647149443198256, 16⟩, ⟨4283177772395120, -1391688820718176, 16⟩]
theorem root00_checked : Trigonometric.cisCheck ((0:ℚ)/20) ((roots 0).toRectangle 52) = true := by decide +kernel
theorem root01_checked : Trigonometric.cisCheck ((1:ℚ)/20) ((roots 1).toRectangle 52) = true := by decide +kernel
theorem root02_checked : Trigonometric.cisCheck ((2:ℚ)/20) ((roots 2).toRectangle 52) = true := by decide +kernel
theorem root03_checked : Trigonometric.cisCheck ((3:ℚ)/20) ((roots 3).toRectangle 52) = true := by decide +kernel
theorem root04_checked : Trigonometric.cisCheck ((4:ℚ)/20) ((roots 4).toRectangle 52) = true := by decide +kernel
theorem root05_checked : Trigonometric.cisCheck ((5:ℚ)/20) ((roots 5).toRectangle 52) = true := by decide +kernel
theorem root06_checked : Trigonometric.cisCheck ((6:ℚ)/20) ((roots 6).toRectangle 52) = true := by decide +kernel
theorem root07_checked : Trigonometric.cisCheck ((7:ℚ)/20) ((roots 7).toRectangle 52) = true := by decide +kernel
theorem root08_checked : Trigonometric.cisCheck ((8:ℚ)/20) ((roots 8).toRectangle 52) = true := by decide +kernel
theorem root09_checked : Trigonometric.cisCheck ((9:ℚ)/20) ((roots 9).toRectangle 52) = true := by decide +kernel
theorem root10_checked : Trigonometric.cisCheck ((10:ℚ)/20) ((roots 10).toRectangle 52) = true := by decide +kernel
theorem root11_checked : Trigonometric.cisCheck ((11:ℚ)/20) ((roots 11).toRectangle 52) = true := by decide +kernel
theorem root12_checked : Trigonometric.cisCheck ((12:ℚ)/20) ((roots 12).toRectangle 52) = true := by decide +kernel
theorem root13_checked : Trigonometric.cisCheck ((13:ℚ)/20) ((roots 13).toRectangle 52) = true := by decide +kernel
theorem root14_checked : Trigonometric.cisCheck ((14:ℚ)/20) ((roots 14).toRectangle 52) = true := by decide +kernel
theorem root15_checked : Trigonometric.cisCheck ((15:ℚ)/20) ((roots 15).toRectangle 52) = true := by decide +kernel
theorem root16_checked : Trigonometric.cisCheck ((16:ℚ)/20) ((roots 16).toRectangle 52) = true := by decide +kernel
theorem root17_checked : Trigonometric.cisCheck ((17:ℚ)/20) ((roots 17).toRectangle 52) = true := by decide +kernel
theorem root18_checked : Trigonometric.cisCheck ((18:ℚ)/20) ((roots 18).toRectangle 52) = true := by decide +kernel
theorem root19_checked : Trigonometric.cisCheck ((19:ℚ)/20) ((roots 19).toRectangle 52) = true := by decide +kernel
theorem roots_checked (n : Fin 20) : Trigonometric.cisCheck ((n.val:ℚ)/20) ((roots n).toRectangle 52) = true := by
  fin_cases n
  · exact root00_checked
  · exact root01_checked
  · exact root02_checked
  · exact root03_checked
  · exact root04_checked
  · exact root05_checked
  · exact root06_checked
  · exact root07_checked
  · exact root08_checked
  · exact root09_checked
  · exact root10_checked
  · exact root11_checked
  · exact root12_checked
  · exact root13_checked
  · exact root14_checked
  · exact root15_checked
  · exact root16_checked
  · exact root17_checked
  · exact root18_checked
  · exact root19_checked
end Maxwell.Certificate.GlobalWitness
