<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Layer Order (Generated)

This file is generated from `scripts/lib/layers.sh` by `scripts/gen/write_layer_order_legend.sh`.

Policy rule: higher layers may import lower layers; lower layers may not import higher layers.

Layers (low -> high):
1. `Host` (rank 0)
2. `Prelude` (rank 1)
3. `Syntax` (rank 2)
4. `LT` (rank 3)
5. `Ports` (rank 4)
6. `Adapters` (rank 5)
7. `Apps` (rank 6)
8. `API` (rank 7)
9. `Checks` (rank 8)
