import Maxwell.Certificate.LowCompressionWitness.LowerRow00
import Maxwell.Certificate.LowCompressionWitness.LowerRow01
import Maxwell.Certificate.LowCompressionWitness.LowerRow02
import Maxwell.Certificate.LowCompressionWitness.LowerRow03
import Maxwell.Certificate.LowCompressionWitness.LowerRow04
import Maxwell.Certificate.LowCompressionWitness.LowerRow05
import Maxwell.Certificate.LowCompressionWitness.LowerRow06
import Maxwell.Certificate.LowCompressionWitness.LowerRow07
import Maxwell.Certificate.LowCompressionWitness.LowerRow08
import Maxwell.Certificate.LowCompressionWitness.LowerRow09
import Maxwell.Certificate.LowCompressionWitness.LowerRow10
import Maxwell.Certificate.LowCompressionWitness.LowerRow11
import Maxwell.Certificate.LowCompressionWitness.LowerRow12
import Maxwell.Certificate.LowCompressionWitness.LowerRow13
import Maxwell.Certificate.LowCompressionWitness.LowerRow14
import Maxwell.Certificate.LowCompressionWitness.LowerRow15
import Maxwell.Certificate.LowCompressionWitness.LowerRow16
import Maxwell.Certificate.LowCompressionWitness.LowerRow17
import Maxwell.Certificate.LowCompressionWitness.LowerRow18
import Maxwell.Certificate.LowCompressionWitness.LowerRow19
import Maxwell.Certificate.LowCompressionWitness.LowerRow20
import Maxwell.Certificate.LowCompressionWitness.LowerRow21
import Maxwell.Certificate.LowCompressionWitness.LowerRow22
import Maxwell.Certificate.LowCompressionWitness.LowerRow23
import Maxwell.Certificate.LowCompressionWitness.LowerRow24
import Maxwell.Certificate.LowCompressionWitness.LowerRow25
import Maxwell.Certificate.LowCompressionWitness.LowerRow26
import Maxwell.Certificate.LowCompressionWitness.LowerRow27
namespace Maxwell.Certificate.LowCompressionWitness
theorem LowerDotCheck_all (i j : Fin 28) : LowerDotCheck i j = true := by
  fin_cases i
  · exact LowerDotCheck_row0 j
  · exact LowerDotCheck_row1 j
  · exact LowerDotCheck_row2 j
  · exact LowerDotCheck_row3 j
  · exact LowerDotCheck_row4 j
  · exact LowerDotCheck_row5 j
  · exact LowerDotCheck_row6 j
  · exact LowerDotCheck_row7 j
  · exact LowerDotCheck_row8 j
  · exact LowerDotCheck_row9 j
  · exact LowerDotCheck_row10 j
  · exact LowerDotCheck_row11 j
  · exact LowerDotCheck_row12 j
  · exact LowerDotCheck_row13 j
  · exact LowerDotCheck_row14 j
  · exact LowerDotCheck_row15 j
  · exact LowerDotCheck_row16 j
  · exact LowerDotCheck_row17 j
  · exact LowerDotCheck_row18 j
  · exact LowerDotCheck_row19 j
  · exact LowerDotCheck_row20 j
  · exact LowerDotCheck_row21 j
  · exact LowerDotCheck_row22 j
  · exact LowerDotCheck_row23 j
  · exact LowerDotCheck_row24 j
  · exact LowerDotCheck_row25 j
  · exact LowerDotCheck_row26 j
  · exact LowerDotCheck_row27 j
end Maxwell.Certificate.LowCompressionWitness
