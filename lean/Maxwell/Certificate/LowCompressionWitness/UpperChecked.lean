import Maxwell.Certificate.LowCompressionWitness.UpperRow00
import Maxwell.Certificate.LowCompressionWitness.UpperRow01
import Maxwell.Certificate.LowCompressionWitness.UpperRow02
import Maxwell.Certificate.LowCompressionWitness.UpperRow03
import Maxwell.Certificate.LowCompressionWitness.UpperRow04
import Maxwell.Certificate.LowCompressionWitness.UpperRow05
import Maxwell.Certificate.LowCompressionWitness.UpperRow06
import Maxwell.Certificate.LowCompressionWitness.UpperRow07
import Maxwell.Certificate.LowCompressionWitness.UpperRow08
import Maxwell.Certificate.LowCompressionWitness.UpperRow09
import Maxwell.Certificate.LowCompressionWitness.UpperRow10
import Maxwell.Certificate.LowCompressionWitness.UpperRow11
import Maxwell.Certificate.LowCompressionWitness.UpperRow12
import Maxwell.Certificate.LowCompressionWitness.UpperRow13
import Maxwell.Certificate.LowCompressionWitness.UpperRow14
import Maxwell.Certificate.LowCompressionWitness.UpperRow15
import Maxwell.Certificate.LowCompressionWitness.UpperRow16
import Maxwell.Certificate.LowCompressionWitness.UpperRow17
import Maxwell.Certificate.LowCompressionWitness.UpperRow18
import Maxwell.Certificate.LowCompressionWitness.UpperRow19
import Maxwell.Certificate.LowCompressionWitness.UpperRow20
import Maxwell.Certificate.LowCompressionWitness.UpperRow21
import Maxwell.Certificate.LowCompressionWitness.UpperRow22
import Maxwell.Certificate.LowCompressionWitness.UpperRow23
import Maxwell.Certificate.LowCompressionWitness.UpperRow24
import Maxwell.Certificate.LowCompressionWitness.UpperRow25
import Maxwell.Certificate.LowCompressionWitness.UpperRow26
import Maxwell.Certificate.LowCompressionWitness.UpperRow27
namespace Maxwell.Certificate.LowCompressionWitness
theorem UpperDotCheck_all (i j : Fin 28) : UpperDotCheck i j = true := by
  fin_cases i
  · exact UpperDotCheck_row0 j
  · exact UpperDotCheck_row1 j
  · exact UpperDotCheck_row2 j
  · exact UpperDotCheck_row3 j
  · exact UpperDotCheck_row4 j
  · exact UpperDotCheck_row5 j
  · exact UpperDotCheck_row6 j
  · exact UpperDotCheck_row7 j
  · exact UpperDotCheck_row8 j
  · exact UpperDotCheck_row9 j
  · exact UpperDotCheck_row10 j
  · exact UpperDotCheck_row11 j
  · exact UpperDotCheck_row12 j
  · exact UpperDotCheck_row13 j
  · exact UpperDotCheck_row14 j
  · exact UpperDotCheck_row15 j
  · exact UpperDotCheck_row16 j
  · exact UpperDotCheck_row17 j
  · exact UpperDotCheck_row18 j
  · exact UpperDotCheck_row19 j
  · exact UpperDotCheck_row20 j
  · exact UpperDotCheck_row21 j
  · exact UpperDotCheck_row22 j
  · exact UpperDotCheck_row23 j
  · exact UpperDotCheck_row24 j
  · exact UpperDotCheck_row25 j
  · exact UpperDotCheck_row26 j
  · exact UpperDotCheck_row27 j
end Maxwell.Certificate.LowCompressionWitness
