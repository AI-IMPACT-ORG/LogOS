<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Strictification Inventory (Generated)

Generated from `scripts/strictification_contract_manifest.tsv`.

| Module | Strict object | Downgrade to `≈` | Downgrade to `⊑` | Law or anchor |
| --- | --- | --- | --- | --- |
| `LogOS.LT.BoundaryImplementation.Strictification` | `StrictBoundaryImplementation` | `toApproxBoundaryImplementation` | `toUnderBoundaryImplementation` | `decode-implementsBoundary` |
| `LogOS.LT.Hom.Strictification` | `KernelHom≡` | `strict→approx` | `strict→under` | `decode-mapCode≡` |
| `LogOS.LT.TypeTheory.Strictification` | `Tm≡` | `strictTm→approx` | `strictTm→under` | `decode-tm≡` |
| `LogOS.LT.Theorems.ArchitecturalNormalFormStrictification` | `ArchitecturalNormalFormStrictification` | `refinementHalf` | `-` | `architecturalNormalFormStrictification` |
