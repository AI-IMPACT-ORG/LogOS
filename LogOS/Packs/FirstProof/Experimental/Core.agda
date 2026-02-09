{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.FirstProof.Experimental.Core where

-- Curated, experimental scaffold for the FirstProof challenge.
--
-- This surface is intentionally assumption-first: each question exposes
-- conditionals and typed reasoning traces that can be strengthened iteratively.

open import LogOS.Packs.Trust using (PackTrust; experimental)

packTrust : PackTrust
packTrust = record { level = experimental }

import LogOS.Packs.FirstProof.Experimental.QuestionScaffold as QuestionScaffoldₜ
module QuestionScaffold = QuestionScaffoldₜ

import LogOS.Packs.FirstProof.Experimental.Questions.All as Questionsₜ
module Questions = Questionsₜ
