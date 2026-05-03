# FWL Manim Animation

This directory contains a Manim walkthrough of the formal structure of
`HansenEconometrics/Chapter3FWL.lean`.

Render the scene from the repository root with:

```bash
source .venv/bin/activate
uv run --active manim -pql --media_dir animations/media animations/fwl_structure.py FWLStructure
```

For a higher-quality render, use `-pqh` instead of `-pql`.

Generate and splice in the voiceover with:

```bash
source .venv/bin/activate
uv run --active python animations/fwl_voiceover.py
```

This writes `animations/media/videos/fwl_structure/1080p15/FWLStructure_voiceover.mp4`.

The animation is organized around the Lean proof dependencies:

- partitioned full-regression normal equations;
- the annihilator identity `M1 X1 = 0`;
- residualized data `M1 y` and `M1 X2`;
- the auxiliary normal equations for the second full coefficient block;
- uniqueness of OLS coefficients from normal equations;
- equality of the FWL and full-regression residuals;
- the sequential residual-maker identity.
