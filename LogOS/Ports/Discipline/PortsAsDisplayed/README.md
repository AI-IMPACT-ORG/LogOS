<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# PortsAsDisplayed

Local navigator for the physical-port displayed-packaging discipline subtree.

- `Core.agda`: import-only gate index for the explicit definitional discipline modules.
- `Budget.agda`, `Deutsch.agda`, `PreQuantum.agda`: harmless witness modules for the corresponding packaging checks.
- `BudgetDefinitional.agda`, `DeutschDefinitional.agda`, `PreQuantumDefinitional.agda`: explicit equality-lane proofs that the canonical port 2-cats are displayed/Σ-totalised in the expected way.
- `Local.agda`: Deutsch-style local product discipline facts.

The default public entrypoint is `LogOS/Ports/Discipline/PortsAsDisplayed.agda`.
