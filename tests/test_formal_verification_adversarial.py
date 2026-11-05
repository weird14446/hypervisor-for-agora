"""Pytest integration for formal verification SMT adversarial challenges.

Empirically challenges:
- formal-verification/verify_network_isolation.py
- formal-verification/verify_state_confinement.py
"""
import subprocess
import sys
from pathlib import Path
import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]
CHALLENGE_SCRIPT = REPO_ROOT / 'formal-verification' / 'adversarial_challenge.py'

def test_smt_adversarial_challenges():
    """Runs all 124 Z3 SMT adversarial stress tests to confirm strict UNSAT / SAT bounds."""
    res = subprocess.run(
        [sys.executable, str(CHALLENGE_SCRIPT)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=60
    )
    assert res.returncode == 0, f"Adversarial challenges failed:\n{res.stdout}\n{res.stderr}"
    assert "Passed:              124" in res.stdout
    assert "Failed:              0" in res.stdout
