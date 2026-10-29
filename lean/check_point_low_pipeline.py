# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Use the common single-worker compiler with an independent point-low ledger."""
from pathlib import Path
import check_fft_stage_proposals as runner
runner.EVIDENCE=Path(__file__).resolve().parent/'evidence/point_low_pipeline'
if __name__=='__main__':
    runner.main()
