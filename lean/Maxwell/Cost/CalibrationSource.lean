import Maxwell.Cost.CalibrationSource.ProducerInputs
import Maxwell.Cost.CalibrationSource.ProducerRun
import Maxwell.Green.CalibrationCommonPairing

/-! Actual sparse calibration sources from the shared stored qhat.

`Producer.executes_inputs` computes every translated radix address and
repackages the retained signed coefficients into the calibration word width,
starting from arbitrary sparse-array memory. `sourceData_records` and
`sourceData_values` bind those exact arrays to the physical translated source.
`Producer.run` charges the compiled Boolean program; `costCap_le` gives a
polynomial bound. `CalibrationCommonPairing` retains the original shared
source denominators through the actual inverse polynomial and scalar pairing.
-/
