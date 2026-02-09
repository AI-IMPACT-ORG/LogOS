#!/usr/bin/env python3
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Iterator, NamedTuple


ROOT = Path(__file__).resolve().parents[1]

# Match only actual import lines to avoid comments/documentation.
IMPORT_RE = re.compile(r"^\s*(?:open\s+import|import)\s+([A-Za-z0-9_.']+)")
FENCE_START_RE = re.compile(r"^\s*```\s*agda\s*$")
FENCE_END_RE = re.compile(r"^\s*```\s*$")


class Roots(NamedTuple):
    api: set[str]
    pack_surfaces: set[str]
    tests: set[str]
    examples: set[str]
    docs: set[str]


@dataclass(frozen=True)
class Node:
    module: str
    path: Path | None
    kind: str  # agda | lagda | external
    category: str


LAYER_ORDER: dict[str, int] = {
    # mirrors scripts/layer_order_check.sh (API intentionally excluded there)
    "Host": 0,
    "Prelude": 1,
    "Base": 2,
    "Syntax": 2,
    "Algebra": 2,
    "Free": 2,
    "Minimal": 3,
    "Kernel": 4,
    "QAdapters": 4,
    "Computation": 4,
    "Axioms": 4,
    "MetaLanguage": 4,
    "Boundary": 5,
    "Ports": 5,
    "Adapters": 5,
    "System": 5,
    "Theorems": 6,
    "ZFC": 7,
    "UniversalIR": 7,
    "Universality": 7,
    "Complexity": 7,
    "InfoTheory": 7,
    "ObjectLogic": 7,
    "Domain": 8,
    "Packs": 9,
    # API is a curated surface “beside” the stack; keep it visually distinct.
    "API": 10,
    # non-LogOS roots
    "docs": 11,
    "Tests": 12,
    "Examples": 13,
}


PALETTE: dict[str, str] = {
    "Host": "#F3E8FF",
    "Prelude": "#EDE9FE",
    "Base": "#E0E7FF",
    "Syntax": "#E0E7FF",
    "Algebra": "#E0E7FF",
    "Free": "#E0E7FF",
    "Minimal": "#DBEAFE",
    "Kernel": "#D1FAE5",
    "QAdapters": "#D1FAE5",
    "Computation": "#D1FAE5",
    "Axioms": "#D1FAE5",
    "MetaLanguage": "#D1FAE5",
    "Boundary": "#FEF3C7",
    "Ports": "#FEF3C7",
    "Adapters": "#FEF3C7",
    "System": "#FEF3C7",
    "Theorems": "#FFE4E6",
    "ZFC": "#FEE2E2",
    "UniversalIR": "#FEE2E2",
    "Universality": "#FEE2E2",
    "Complexity": "#FEE2E2",
    "InfoTheory": "#FEE2E2",
    "ObjectLogic": "#FEE2E2",
    "Domain": "#FDE68A",
    "Packs": "#E5E7EB",
    "API": "#E5E7EB",
    "docs": "#E5E7EB",
    "Tests": "#E5E7EB",
    "Examples": "#E5E7EB",
    "external": "#FFFFFF",
}


def die(msg: str) -> None:
    print(f"depgraph: {msg}", file=sys.stderr)
    raise SystemExit(2)


def is_ignored_path(path: Path) -> bool:
    parts = set(path.parts)
    return "_build" in parts or ".git" in parts or ".agda" in parts


def module_from_relpath(rel: Path) -> str:
    if rel.name.endswith(".agda"):
        stem = rel.with_suffix("")
        return ".".join(stem.parts)
    if rel.name.endswith(".lagda.md"):
        rel_str = rel.as_posix()
        stem_str = rel_str[: -len(".lagda.md")]
        stem = Path(stem_str)
        return ".".join(stem.parts)
    raise ValueError(f"unsupported file: {rel}")


def category_of_module(module: str) -> str:
    parts = module.split(".")
    if parts and parts[0] == "LogOS":
        return parts[1] if len(parts) > 1 else "LogOS"
    if parts and parts[0] in {"docs", "Tests", "Examples"}:
        return parts[0]
    return parts[0] if parts else module


def iter_agda_imports_from_lines(lines: Iterable[str]) -> Iterator[str]:
    for line in lines:
        match = IMPORT_RE.match(line)
        if match:
            yield match.group(1)


def read_imports_agda(path: Path) -> list[str]:
    return list(iter_agda_imports_from_lines(path.read_text(encoding="utf-8").splitlines()))


def iter_lagda_agda_block_lines(path: Path) -> Iterator[str]:
    inside = False
    for line in path.read_text(encoding="utf-8").splitlines():
        if FENCE_START_RE.match(line):
            inside = True
            continue
        if inside and FENCE_END_RE.match(line):
            inside = False
            continue
        if inside:
            yield line


def read_imports_lagda(path: Path) -> list[str]:
    return list(iter_agda_imports_from_lines(iter_lagda_agda_block_lines(path)))


def discover_nodes(
    *,
    include_docs: bool,
    include_tests: bool,
    include_examples: bool,
) -> dict[str, Node]:
    nodes: dict[str, Node] = {}

    def add_node(rel: Path, *, kind: str) -> None:
        module = module_from_relpath(rel)
        if module in nodes:
            die(f"duplicate module name {module} from {rel} and {nodes[module].path}")
        cat = category_of_module(module)
        nodes[module] = Node(module=module, path=ROOT / rel, kind=kind, category=cat)

    roots: list[Path] = []

    for base in ("LogOS",):
        base_path = ROOT / base
        if base_path.is_dir():
            roots.append(base_path)

    if include_tests and (ROOT / "Tests").is_dir():
        roots.append(ROOT / "Tests")
    if include_examples and (ROOT / "Examples").is_dir():
        roots.append(ROOT / "Examples")
    if include_docs and (ROOT / "docs").is_dir():
        roots.append(ROOT / "docs")

    for base_path in roots:
        for path in base_path.rglob("*.agda"):
            if is_ignored_path(path):
                continue
            add_node(path.relative_to(ROOT), kind="agda")

    if include_docs and (ROOT / "docs").is_dir():
        for path in (ROOT / "docs").rglob("*.lagda.md"):
            if is_ignored_path(path):
                continue
            add_node(path.relative_to(ROOT), kind="lagda")

    return nodes


def discover_roots(nodes: dict[str, Node]) -> Roots:
    api_roots: set[str] = set()
    for path in (ROOT / "LogOS" / "API").glob("*.agda"):
        rel = path.relative_to(ROOT)
        mod = module_from_relpath(rel)
        if mod in nodes:
            api_roots.add(mod)

    pack_surfaces: set[str] = set()
    for path in (ROOT / "LogOS" / "Packs").rglob("Surface.agda"):
        rel = path.relative_to(ROOT)
        mod = module_from_relpath(rel)
        if mod in nodes:
            pack_surfaces.add(mod)

    tests: set[str] = set()
    for rel in (
        Path("Tests/All.agda"),
        Path("Tests/Vacuity.agda"),
        Path("Tests/Correctness.agda"),
    ):
        path = ROOT / rel
        if not path.exists():
            continue
        mod = module_from_relpath(rel)
        if mod in nodes:
            tests.add(mod)

    examples: set[str] = set()
    for path in (ROOT / "Examples").glob("*.agda"):
        rel = path.relative_to(ROOT)
        mod = module_from_relpath(rel)
        if mod in nodes:
            examples.add(mod)

    docs: set[str] = set()
    for mod, node in nodes.items():
        if node.category == "docs":
            docs.add(mod)

    return Roots(
        api=api_roots,
        pack_surfaces=pack_surfaces,
        tests=tests,
        examples=examples,
        docs=docs,
    )


def build_dep_graph(
    nodes: dict[str, Node],
    *,
    include_external: bool,
) -> tuple[dict[str, Node], dict[str, set[str]]]:
    all_nodes: dict[str, Node] = dict(nodes)
    deps: dict[str, set[str]] = defaultdict(set)

    for mod, node in nodes.items():
        if node.path is None:
            continue
        if node.kind == "agda":
            imported = read_imports_agda(node.path)
        elif node.kind == "lagda":
            imported = read_imports_lagda(node.path)
        else:
            imported = []

        for dep in imported:
            if dep in nodes:
                deps[mod].add(dep)
                continue
            if include_external and dep not in all_nodes:
                all_nodes[dep] = Node(module=dep, path=None, kind="external", category="external")
                deps[mod].add(dep)

    return all_nodes, deps


def reverse_deps(deps: dict[str, set[str]]) -> dict[str, set[str]]:
    rev: dict[str, set[str]] = defaultdict(set)
    for src, dsts in deps.items():
        for dst in dsts:
            rev[dst].add(src)
    return rev


def topo_sort_dag(modules: set[str], deps: dict[str, set[str]]) -> list[str]:
    succ: dict[str, set[str]] = {
        u: {v for v in deps.get(u, set()) if v in modules} for u in modules
    }
    indeg: dict[str, int] = {u: 0 for u in modules}
    for u, dsts in succ.items():
        for v in dsts:
            indeg[v] += 1

    q: deque[str] = deque(sorted([u for u, d in indeg.items() if d == 0]))
    out: list[str] = []
    while q:
        u = q.popleft()
        out.append(u)
        for v in sorted(succ.get(u, ())):
            indeg[v] -= 1
            if indeg[v] == 0:
                q.append(v)

    if len(out) != len(modules):
        die("graph has cycles (cannot transitive-reduce)")
    return out


def transitive_reduce_dag(modules: set[str], deps: dict[str, set[str]]) -> tuple[dict[str, set[str]], int]:
    if not modules:
        return dict(deps), 0

    topo = topo_sort_dag(modules, deps)
    idx: dict[str, int] = {m: i for i, m in enumerate(topo)}

    succ: dict[str, set[str]] = {
        u: {v for v in deps.get(u, set()) if v in modules} for u in modules
    }

    reach: dict[str, int] = {u: 0 for u in modules}
    for u in reversed(topo):
        bits = 0
        for v in succ.get(u, ()):
            bits |= 1 << idx[v]
            bits |= reach[v]
        reach[u] = bits

    reduced: dict[str, set[str]] = {u: set(dsts) for u, dsts in deps.items()}
    removed = 0

    for u in modules:
        union_reach_succ = 0
        for w in succ.get(u, ()):
            union_reach_succ |= reach[w]

        for v in list(succ.get(u, ())):
            if (union_reach_succ >> idx[v]) & 1:
                if u in reduced and v in reduced[u]:
                    reduced[u].remove(v)
                    removed += 1

    # Sanity: reachability among `modules` must be preserved.
    # Compute reachability bitsets in the reduced graph and compare.
    succ_r: dict[str, set[str]] = {
        u: {v for v in reduced.get(u, set()) if v in modules} for u in modules
    }
    reach_r: dict[str, int] = {u: 0 for u in modules}
    for u in reversed(topo):
        bits = 0
        for v in succ_r.get(u, ()):
            bits |= 1 << idx[v]
            bits |= reach_r[v]
        reach_r[u] = bits

    for u in modules:
        if reach_r[u] != reach[u]:
            die(f"transitive reduction sanity check failed at {u}")

    return reduced, removed


def reachable_from(roots: Iterable[str], deps: dict[str, set[str]]) -> set[str]:
    seen: set[str] = set()
    q: deque[str] = deque(roots)
    while q:
        mod = q.popleft()
        if mod in seen:
            continue
        seen.add(mod)
        for dep in deps.get(mod, ()):
            if dep not in seen:
                q.append(dep)
    return seen


def compute_degrees(modules: Iterable[str], deps: dict[str, set[str]]) -> tuple[dict[str, int], dict[str, int]]:
    in_deg: dict[str, int] = {m: 0 for m in modules}
    out_deg: dict[str, int] = {m: 0 for m in modules}
    for src, dsts in deps.items():
        if src not in out_deg:
            continue
        out_deg[src] += len([d for d in dsts if d in in_deg])
        for dst in dsts:
            if dst in in_deg:
                in_deg[dst] += 1
    return in_deg, out_deg


def weakly_connected_components(modules: set[str], deps: dict[str, set[str]]) -> list[set[str]]:
    undirected: dict[str, set[str]] = defaultdict(set)
    for src, dsts in deps.items():
        if src not in modules:
            continue
        for dst in dsts:
            if dst not in modules:
                continue
            undirected[src].add(dst)
            undirected[dst].add(src)

    seen: set[str] = set()
    comps: list[set[str]] = []

    for m in sorted(modules):
        if m in seen:
            continue
        comp: set[str] = set()
        q: deque[str] = deque([m])
        while q:
            x = q.popleft()
            if x in seen:
                continue
            seen.add(x)
            comp.add(x)
            for y in undirected.get(x, ()):
                if y not in seen:
                    q.append(y)
        comps.append(comp)

    comps.sort(key=lambda c: (-len(c), sorted(c)[0]))
    return comps


def strongly_connected_components(modules: set[str], deps: dict[str, set[str]]) -> list[set[str]]:
    # Tarjan SCC (iterative-ish recursion depth is fine for this repo size).
    index = 0
    indices: dict[str, int] = {}
    lowlink: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    result: list[set[str]] = []

    sys.setrecursionlimit(max(10_000, len(modules) * 2))

    def visit(v: str) -> None:
        nonlocal index
        indices[v] = index
        lowlink[v] = index
        index += 1
        stack.append(v)
        on_stack.add(v)

        for w in deps.get(v, ()):
            if w not in modules:
                continue
            if w not in indices:
                visit(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], indices[w])

        if lowlink[v] == indices[v]:
            comp: set[str] = set()
            while True:
                w = stack.pop()
                on_stack.remove(w)
                comp.add(w)
                if w == v:
                    break
            result.append(comp)

    for v in sorted(modules):
        if v not in indices:
            visit(v)

    result.sort(key=lambda c: (-len(c), sorted(c)[0]))
    return result


def dot_escape(s: str) -> str:
    return s.replace("\\", "\\\\").replace('"', '\\"')


def short_label(module: str) -> str:
    parts = module.split(".")
    if len(parts) <= 2:
        return module
    return ".".join(parts[-2:])


def sanitize_id(s: str) -> str:
    out = []
    for ch in s:
        if ch.isalnum():
            out.append(ch)
        else:
            out.append("_")
    return "".join(out)


def write_dot(
    out_path: Path,
    *,
    nodes: dict[str, Node],
    deps: dict[str, set[str]],
    direction: str,
    highlight: dict[str, dict[str, str]] | None = None,
) -> None:
    cats: dict[str, list[str]] = defaultdict(list)
    for mod, node in nodes.items():
        cats[node.category].append(mod)

    # Stable-ish ordering: by layer, then lexicographically.
    def cat_key(cat: str) -> tuple[int, str]:
        return (LAYER_ORDER.get(cat, 100), cat)

    highlight = highlight or {}

    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as f:
        f.write("digraph G {\n")
        f.write('  graph [rankdir=TB, overlap=false, splines=true, fontsize=10, fontname="Helvetica"];\n')
        f.write('  node  [shape=box, style="filled", fontsize=10, fontname="Helvetica", margin="0.06,0.04"];\n')
        f.write('  edge  [color="#9CA3AF", arrowsize=0.6];\n')

        for cat in sorted(cats.keys(), key=cat_key):
            cluster_id = sanitize_id(cat)
            color = PALETTE.get(cat, "#FFFFFF")
            f.write(f'  subgraph "cluster_{cluster_id}" {{\n')
            f.write(f'    label="{dot_escape(cat)}";\n')
            f.write(f'    style="filled";\n')
            f.write(f'    color="{color}";\n')
            f.write('    fontname="Helvetica"; fontsize=12;\n')

            for mod in sorted(cats[cat]):
                node = nodes[mod]
                attrs = {
                    "label": short_label(mod),
                    "tooltip": mod if node.path is None else f"{mod}\\n{node.path.relative_to(ROOT)}",
                    "fillcolor": PALETTE.get(cat, "#FFFFFF") if node.kind != "external" else PALETTE["external"],
                }
                attrs.update(highlight.get(mod, {}))
                attr_str = ", ".join(f'{k}="{dot_escape(v)}"' for k, v in attrs.items())
                f.write(f'    "{dot_escape(mod)}" [{attr_str}];\n')
            f.write("  }\n")

        for src, dsts in sorted(deps.items(), key=lambda kv: kv[0]):
            for dst in sorted(dsts):
                if src not in nodes or dst not in nodes:
                    continue
                if direction == "depends":
                    a, b = src, dst
                elif direction == "used-by":
                    a, b = dst, src
                else:
                    raise ValueError(f"unknown direction: {direction}")
                f.write(f'  "{dot_escape(a)}" -> "{dot_escape(b)}";\n')

        f.write("}\n")


def write_layer_dot(
    out_path: Path,
    *,
    nodes: dict[str, Node],
    deps: dict[str, set[str]],
    direction: str,
) -> None:
    cats: set[str] = set(n.category for n in nodes.values())
    edges: set[tuple[str, str]] = set()
    for src, dsts in deps.items():
        if src not in nodes:
            continue
        src_cat = nodes[src].category
        for dst in dsts:
            if dst not in nodes:
                continue
            dst_cat = nodes[dst].category
            if src_cat == dst_cat:
                continue
            if direction == "depends":
                edges.add((src_cat, dst_cat))
            elif direction == "used-by":
                edges.add((dst_cat, src_cat))
            else:
                raise ValueError(f"unknown direction: {direction}")

    def cat_key(cat: str) -> tuple[int, str]:
        return (LAYER_ORDER.get(cat, 100), cat)

    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as f:
        f.write("digraph Layers {\n")
        f.write('  graph [rankdir=TB, overlap=false, splines=true, fontsize=12, fontname="Helvetica"];\n')
        f.write('  node  [shape=box, style="filled", fontsize=12, fontname="Helvetica", margin="0.12,0.08"];\n')
        f.write('  edge  [color="#374151", arrowsize=0.8];\n')

        for cat in sorted(cats, key=cat_key):
            fill = PALETTE.get(cat, "#FFFFFF")
            f.write(f'  "{dot_escape(cat)}" [fillcolor="{fill}"];\n')

        for a, b in sorted(edges, key=lambda e: (cat_key(e[0]), cat_key(e[1]))):
            f.write(f'  "{dot_escape(a)}" -> "{dot_escape(b)}";\n')

        f.write("}\n")


def write_graphml(out_path: Path, *, nodes: dict[str, Node], deps: dict[str, set[str]]) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as f:
        f.write('<?xml version="1.0" encoding="UTF-8"?>\n')
        f.write('<graphml xmlns="http://graphml.graphdrawing.org/xmlns">\n')
        f.write('  <key id="category" for="node" attr.name="category" attr.type="string"/>\n')
        f.write('  <key id="kind" for="node" attr.name="kind" attr.type="string"/>\n')
        f.write('  <key id="path" for="node" attr.name="path" attr.type="string"/>\n')
        f.write('  <graph id="G" edgedefault="directed">\n')
        for mod, node in sorted(nodes.items(), key=lambda kv: kv[0]):
            f.write(f'    <node id="{mod}">\n')
            f.write(f'      <data key="category">{node.category}</data>\n')
            f.write(f'      <data key="kind">{node.kind}</data>\n')
            rel = "" if node.path is None else node.path.relative_to(ROOT).as_posix()
            f.write(f'      <data key="path">{rel}</data>\n')
            f.write("    </node>\n")
        eid = 0
        for src, dsts in sorted(deps.items(), key=lambda kv: kv[0]):
            for dst in sorted(dsts):
                if src not in nodes or dst not in nodes:
                    continue
                f.write(f'    <edge id="e{eid}" source="{src}" target="{dst}"/>\n')
                eid += 1
        f.write("  </graph>\n")
        f.write("</graphml>\n")


def render_svg(dot_path: Path, *, svg_path: Path, layout: str) -> None:
    svg_path.parent.mkdir(parents=True, exist_ok=True)
    cmd = [layout, "-Tsvg", str(dot_path), "-o", str(svg_path)]
    try:
        subprocess.run(cmd, check=True, cwd=ROOT)
    except FileNotFoundError:
        die(f"graphviz layout tool not found: {layout}")
    except subprocess.CalledProcessError as e:
        die(f"graphviz render failed: {' '.join(cmd)} (exit={e.returncode})")


def write_report(
    out_path: Path,
    *,
    nodes: dict[str, Node],
    deps: dict[str, set[str]],
    roots: Roots,
) -> dict[str, object]:
    internal = {m for m, n in nodes.items() if n.kind != "external"}

    reachable_api = reachable_from(sorted(roots.api), deps)
    reachable_packs = reachable_from(sorted(roots.pack_surfaces), deps)
    reachable_public = reachable_from(sorted(roots.api | roots.pack_surfaces), deps)
    reachable_tests = reachable_from(sorted(roots.tests), deps)
    reachable_examples = reachable_from(sorted(roots.examples), deps)
    reachable_docs = reachable_from(sorted(roots.docs), deps)
    reachable_any = reachable_from(
        sorted(roots.api | roots.pack_surfaces | roots.tests | roots.examples | roots.docs),
        deps,
    )

    in_deg, out_deg = compute_degrees(internal, deps)

    dead = sorted(internal - reachable_any)
    public_unused = sorted(internal - reachable_public)
    used_only_by_docs = sorted((reachable_docs - reachable_public) - reachable_tests)
    used_only_by_tests = sorted((reachable_tests - reachable_public) - reachable_docs)
    untested_non_docs = sorted((internal - reachable_tests) - roots.docs)

    root_modules = roots.api | roots.pack_surfaces | roots.tests | roots.examples | roots.docs
    orphan_non_roots = sorted([m for m in internal if in_deg.get(m, 0) == 0 and m not in root_modules])

    wcc = weakly_connected_components(internal, deps)
    scc = strongly_connected_components(internal, deps)
    nontrivial_scc = [c for c in scc if len(c) > 1]

    top_in = sorted(in_deg.items(), key=lambda kv: (-kv[1], kv[0]))[:25]
    top_out = sorted(out_deg.items(), key=lambda kv: (-kv[1], kv[0]))[:25]

    def fmt_list(items: list[str], limit: int = 60) -> str:
        if not items:
            return "_(none)_\n"
        head = items[:limit]
        more = len(items) - len(head)
        lines = [f"- `{m}`" for m in head]
        if more > 0:
            lines.append(f"- _… and {more} more_")
        return "\n".join(lines) + "\n"

    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as f:
        f.write("# Dependency Graph Report (Agda import graph)\n\n")
        f.write(f"- Repo root: `{ROOT}`\n")
        f.write(f"- Internal modules: **{len(internal)}**\n")
        f.write(f"- Internal edges: **{sum(len(v) for k, v in deps.items() if k in internal)}**\n")
        f.write("\n")

        f.write("## Roots (used for reachability)\n\n")
        f.write(f"- API roots: {len(roots.api)}\n")
        f.write(f"- Pack surfaces: {len(roots.pack_surfaces)}\n")
        f.write(f"- Tests: {len(roots.tests)}\n")
        f.write(f"- Examples: {len(roots.examples)}\n")
        f.write(f"- Docs modules: {len(roots.docs)}\n\n")

        f.write("## Reachability snapshots\n\n")
        f.write(f"- Reachable from API roots: **{len(reachable_api & internal)}** modules\n")
        f.write(f"- Reachable from pack surfaces: **{len(reachable_packs & internal)}** modules\n")
        f.write(f"- Reachable from public roots (API ∪ packs): **{len(reachable_public & internal)}** modules\n")
        f.write(f"- Reachable from tests: **{len(reachable_tests & internal)}** modules\n")
        f.write(f"- Reachable from docs: **{len(reachable_docs & internal)}** modules\n")
        f.write(f"- Reachable from examples: **{len(reachable_examples & internal)}** modules\n\n")

        f.write("## Potential “bubbles”\n\n")
        f.write("### Dead code (unreachable from any roots)\n\n")
        f.write(
            "_Roots = API roots ∪ pack surfaces ∪ test entrypoints (Tests.All/Vacuity/Correctness) ∪ Examples ∪ docs modules._\n\n"
        )
        f.write(fmt_list(dead, limit=80))
        f.write("\n")

        f.write("### Orphan modules (no internal dependents, excluding roots)\n\n")
        f.write(fmt_list(orphan_non_roots, limit=80))
        f.write("\n")

        f.write("### Modules not used by public surfaces (API ∪ Packs)\n\n")
        f.write(fmt_list(public_unused, limit=80))
        f.write("\n")

        f.write("### Used only by docs (and not by public surfaces/tests)\n\n")
        f.write(fmt_list(used_only_by_docs, limit=80))
        f.write("\n")

        f.write("### Used only by tests (and not by public surfaces/docs)\n\n")
        f.write(fmt_list(used_only_by_tests, limit=80))
        f.write("\n")

        f.write("### Not covered by `Tests.All` (excluding docs modules)\n\n")
        f.write(fmt_list(untested_non_docs, limit=80))
        f.write("\n")

        f.write("## Connectivity\n\n")
        f.write(f"- Weakly connected components: **{len(wcc)}** (largest = {len(wcc[0]) if wcc else 0})\n")
        small = [c for c in wcc if len(c) <= 5]
        f.write(f"- Small components (≤ 5 modules): **{len(small)}**\n\n")
        if small:
            f.write("Small components (≤ 5):\n")
            for comp in small[:20]:
                f.write(f"- {len(comp)}: " + ", ".join(f"`{m}`" for m in sorted(comp)) + "\n")
            if len(small) > 20:
                f.write(f"- _… and {len(small) - 20} more_\n")
            f.write("\n")

        f.write("## Cycles (SCCs)\n\n")
        f.write(f"- Strongly connected components: **{len(scc)}**\n")
        f.write(f"- Non-trivial SCCs (>1 module): **{len(nontrivial_scc)}**\n\n")
        if nontrivial_scc:
            for comp in nontrivial_scc[:25]:
                mods = sorted(comp)
                f.write(f"- {len(mods)}: " + ", ".join(f"`{m}`" for m in mods[:12]) + ("\n" if len(mods) <= 12 else f", _… +{len(mods)-12}_\n"))
            if len(nontrivial_scc) > 25:
                f.write(f"- _… and {len(nontrivial_scc) - 25} more_\n")
        else:
            f.write("_(no import cycles detected)_\n")
        f.write("\n")

        f.write("## Top hubs\n\n")
        f.write("### Highest fan-in (most depended-on)\n\n")
        for mod, deg in top_in:
            f.write(f"- `{mod}`: {deg}\n")
        f.write("\n")
        f.write("### Highest fan-out (largest import surface)\n\n")
        for mod, deg in top_out:
            f.write(f"- `{mod}`: {deg}\n")
        f.write("\n")

    return {
        "counts": {
            "internal_nodes": len(internal),
            "internal_edges": sum(len(v) for k, v in deps.items() if k in internal),
            "wcc": len(wcc),
            "scc": len(scc),
            "nontrivial_scc": len(nontrivial_scc),
        },
        "sets": {
            "dead": dead,
            "public_unused": public_unused,
            "used_only_by_docs": used_only_by_docs,
            "used_only_by_tests": used_only_by_tests,
            "untested_non_docs": untested_non_docs,
            "orphan_non_roots": orphan_non_roots,
        },
    }


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description="Generate LogOS Agda import dependency graphs and a report.")
    ap.add_argument("--out-dir", default="_build/depgraph", help="Output directory (default: _build/depgraph)")
    ap.add_argument(
        "--direction",
        choices=("depends", "used-by"),
        default="used-by",
        help='Edge direction in DOT graphs: "depends" = importer→imported, "used-by" = imported→importer (default: used-by)',
    )
    ap.add_argument("--include-external", action="store_true", help="Include external module nodes (Agda.Builtin.*, etc).")
    ap.add_argument("--no-docs", action="store_true", help="Exclude docs modules (.lagda.md and docs/*.agda).")
    ap.add_argument("--no-tests", action="store_true", help="Exclude Tests/*.agda nodes.")
    ap.add_argument("--no-examples", action="store_true", help="Exclude Examples/*.agda nodes.")
    ap.add_argument("--render", action="store_true", help="Also render SVGs via Graphviz.")
    ap.add_argument(
        "--layout",
        default="sfdp",
        help='Graphviz layout tool for SVG rendering (default: sfdp). Examples: "sfdp", "dot", "fdp", "neato".',
    )
    ap.add_argument(
        "--transitive-reduction",
        action="store_true",
        help="Apply transitive reduction (DAG-only) before writing graphs (removes redundant edges while preserving reachability).",
    )
    args = ap.parse_args(argv)

    out_dir = (ROOT / args.out_dir).resolve()
    include_docs = not args.no_docs
    include_tests = not args.no_tests
    include_examples = not args.no_examples

    nodes = discover_nodes(include_docs=include_docs, include_tests=include_tests, include_examples=include_examples)
    roots = discover_roots(nodes)
    all_nodes, deps = build_dep_graph(nodes, include_external=args.include_external)

    removed_edges = 0
    if args.transitive_reduction:
        modules_to_reduce = set(all_nodes.keys())
        deps, removed_edges = transitive_reduce_dag(modules_to_reduce, deps)

    # Highlight public roots in the big graph for navigation.
    highlight: dict[str, dict[str, str]] = {}
    for m in roots.api:
        highlight[m] = {"shape": "doubleoctagon", "fillcolor": "#D1D5DB", "penwidth": "2"}
    for m in roots.pack_surfaces:
        highlight[m] = {"shape": "doubleoctagon", "fillcolor": "#D1D5DB", "penwidth": "2"}
    for m in roots.tests:
        highlight[m] = {"shape": "ellipse", "fillcolor": "#FDE68A", "penwidth": "2"}

    dot_modules = out_dir / "depgraph.modules.dot"
    dot_layers = out_dir / "depgraph.layers.dot"
    graphml = out_dir / "depgraph.modules.graphml"
    report_md = out_dir / "depgraph.report.md"
    report_json = out_dir / "depgraph.report.json"

    write_dot(dot_modules, nodes=all_nodes, deps=deps, direction=args.direction, highlight=highlight)
    write_layer_dot(dot_layers, nodes=all_nodes, deps=deps, direction=args.direction)
    write_graphml(graphml, nodes=all_nodes, deps=deps)
    report_data = write_report(report_md, nodes=all_nodes, deps=deps, roots=roots)
    report_json.write_text(json.dumps(report_data, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if args.render:
        svg_modules = out_dir / "depgraph.modules.svg"
        svg_layers = out_dir / "depgraph.layers.svg"
        render_svg(dot_layers, svg_path=svg_layers, layout="dot")
        render_svg(dot_modules, svg_path=svg_modules, layout=args.layout)

    print(f"depgraph: wrote {dot_modules.relative_to(ROOT)}")
    print(f"depgraph: wrote {dot_layers.relative_to(ROOT)}")
    print(f"depgraph: wrote {graphml.relative_to(ROOT)}")
    print(f"depgraph: wrote {report_md.relative_to(ROOT)}")
    if args.transitive_reduction:
        print(f"depgraph: transitive reduction removed {removed_edges} edges")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
