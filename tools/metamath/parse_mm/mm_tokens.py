#!/usr/bin/env python3
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

from __future__ import annotations

from pathlib import Path
from typing import Iterator, List

from mm_error import MMError


def _iter_raw_tokens(path: Path) -> Iterator[str]:
    try:
        with path.open("r", encoding="utf-8", errors="replace") as f:
            for line in f:
                for tok in line.split():
                    yield tok
    except OSError as e:
        raise MMError(f"failed to open {path}: {e.strerror or e}") from e


class _TokenSource:
    def __init__(self, path: Path):
        self.path = path
        self._it = _iter_raw_tokens(path)
        self._in_comment = False

    def next_token(self) -> str:
        while True:
            tok = next(self._it)  # may raise StopIteration
            if self._in_comment:
                if tok == "$)":
                    self._in_comment = False
                continue
            if tok == "$(":
                self._in_comment = True
                continue
            return tok


class _TokenStack:
    def __init__(self, root: Path):
        self._stack: List[_TokenSource] = [_TokenSource(root)]
        self._include_chain: List[Path] = [root.resolve()]

    def _push(self, path: Path) -> None:
        resolved = path.resolve()
        if resolved in self._include_chain:
            chain = " -> ".join(str(p) for p in self._include_chain + [resolved])
            raise MMError(f"include cycle detected: {chain}")
        self._include_chain.append(resolved)
        self._stack.append(_TokenSource(path))

    def _pop(self) -> None:
        self._stack.pop()
        self._include_chain.pop()

    def pop(self) -> str:
        while True:
            if not self._stack:
                raise StopIteration
            try:
                tok = self._stack[-1].next_token()
            except StopIteration:
                self._pop()
                continue

            if tok != "$[":
                return tok

            # Include: $[ filename $]
            try:
                fname = self._stack[-1].next_token()
            except StopIteration as e:
                raise MMError(f"unexpected EOF after $[ in {self._stack[-1].path}") from e
            try:
                close = self._stack[-1].next_token()
            except StopIteration as e:
                raise MMError(
                    f"unexpected EOF in include after $[ {fname} in {self._stack[-1].path}"
                ) from e
            if close != "$]":
                raise MMError(
                    f"malformed include: expected $] after $[ {fname}, got {close} (in {self._stack[-1].path})"
                )

            inc_path = (self._stack[-1].path.parent / fname).resolve()
            if not inc_path.exists():
                raise MMError(f"included file not found: {inc_path}")
            self._push(inc_path)


def _read_until(ts: _TokenStack, stop: str) -> List[str]:
    out: List[str] = []
    while True:
        try:
            tok = ts.pop()
        except StopIteration as e:
            raise MMError(f"unexpected EOF while scanning until {stop}") from e
        if tok == stop:
            return out
        out.append(tok)

