#!/usr/bin/env python3
"""Generate the module graph of the EpsilonEridani library: modules as nodes, imports as edges.

Three kinds of node go into the graph, in three bands from top to bottom:

* **Entry points**: the upstream modules (Mathlib, Physlib, PhyslibAlpha, TauCeti, ...) that some
  EpsilonEridani module imports directly. They are grouped by the Lake package that provides them,
  and link to their source at the commit `lake-manifest.json` pins. Only direct imports are drawn;
  the upstream libraries' own import structure is out of scope.

* **Modules**: every `EpsilonEridani/**/*.lean` file. An edge `A -> B` means `B` imports `A`, so
  everything flows downstream. Modules whose declarations all live outside the `EpsilonEridani`
  namespace (the `*Extensions.lean` mirrors, say) are flagged as PhyslibAlpha-eligible.

* **Roadmap targets** (optional, `--roadmap-dir`): one node per `## Layer` section of each
  roadmap's `Suggested.lean` in EpsilonEridaniRoadmaps, keyed by the same layer id
  (`roadmap_progress.layer_id`) as the Progress page. An edge `M -> layer` means the layer
  builds on module `M`, in one of two ways:

  - a signature or docstring in that section names a declaration that `M` defines. Names are
    resolved textually against a declaration index built from the sources with
    `lean_source.qualified_declarations`, trying each name as written, under the file's `open`s
    and under `EpsilonEridani`; a name with no indexed match falls back to its longest indexed
    prefix of at least two components, so a field or constructor (`Kin.q`) links to the module
    defining its type (`Kin`). A name with no indexed prefix either (an auto-generated lemma,
    say) draws no edge. This is a best-effort reading, not checked by Lean.
  - the roadmap file imports `M`. Most roadmap files import only the empty `EpsilonEridani`
    root, but a file that imports library modules builds on all of them, so they are linked to
    its first section.

Everything is read from source text, so no build is needed and the Pages workflow can run it
alongside the other chart generators. Outputs, into `--out-dir`:

* `module-graph.json`: the nodes and edges (see `build_graph`), the data the viewer and the
  Graphviz source are drawn from;
* `module-graph.dot`: Graphviz source, one cluster per package and per top-level directory, with
  import edges implied by transitivity left out;
* `module-graph.html`: a local preview of the viewer. The viewer itself is the committed
  `web/static_files/module-graph.html`, which fetches `module-graph.json`; this copy inlines the
  data and the site's `style.css` so that it also opens from `file://`.

Pure stdlib, like the other generators, so CI needs no pip install. The viewer loads cytoscape.js
and dagre from jsDelivr, pinned by subresource-integrity hashes.
"""

from __future__ import annotations

import argparse
import collections
import datetime as dt
import json
import pathlib
import re
import subprocess
import sys

from chart_style import BAR_BG, BG, FONT_FAMILY, MUTED, PALETTE, PANEL, TEXT
from lean_source import qualified_declarations, strip_comments_and_strings
from roadmap_progress import git_head, layer_id

LIB = "EpsilonEridani"
REPO_URL = "https://github.com/eic/EpsilonEridani"
ROADMAP_REPO_URL = "https://github.com/eic/EpsilonEridaniRoadmaps"
DOCS_URL = "https://eic.github.io/EpsilonEridani/docs"
MATHLIB_DOCS_URL = "https://leanprover-community.github.io/mathlib4_docs"
ROADMAP_AREAS = ("EpsilonEridaniRoadmaps", "Completed")
ROADMAP_COLOR = "#fde047"

# Module root -> (display package, lake-manifest package name). Roots not listed are grouped
# under their own name; the core Lean roots have no manifest entry and no source link.
PACKAGES = {
    "Mathlib": ("Mathlib", "mathlib"),
    "Physlib": ("Physlib", "Physlib"),
    "PhyslibAlpha": ("PhyslibAlpha", "Physlib"),
    "QuantumInfo": ("QuantumInfo", "Physlib"),
    "TauCeti": ("TauCeti", "TauCeti"),
    "Batteries": ("Batteries", "batteries"),
    "Aesop": ("Aesop", "aesop"),
    "Qq": ("Qq", "Qq"),
    "Plausible": ("Plausible", "plausible"),
    "ProofWidgets": ("ProofWidgets", "proofwidgets"),
}
PACKAGE_ORDER = ["Mathlib", "Physlib", "PhyslibAlpha", "QuantumInfo", "TauCeti"]

IMPORT_RE = re.compile(
    r"^(?:(?:public|private)\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.'«»]+)\s*$")
# Declaration commands outside `lean_source.DECLARATION_KEYWORDS`, passed to it as extra events
# (as scripts/check-expired-upstream-shims.py does for `alias` and `axiom`).
EXTRA_DECL_RE = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*(?:(?:private|protected|noncomputable|public)\s+)*"
    r"(?:axiom|irreducible_def)\s+(?P<name>[\w'][\w'!?]*(?:\.[\w'][\w'!?]*)*)")
OPEN_RE = re.compile(r"^\s*open\s+(.*)$")
LAYER_RE = re.compile(r"^/-!\s*##\s+(.*)$")
TITLE_RE = re.compile(r"/-!\s*\n?\s*#\s+(.+)")
IDENT_RE = re.compile(r"[\w'!?]+(?:\.[\w'!?]+)*")
TARGET_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*"
                       r"(def|theorem|lemma|abbrev|structure|class|inductive|instance)\b", re.M)


# --- Lean source handling --------------------------------------------------------------------

def parse_imports(text: str) -> list[str]:
    """The modules a Lean file imports in its header."""
    imports = []
    for line in strip_comments_and_strings(text).splitlines():
        s = line.strip()
        if not s or s in ("module", "prelude"):
            continue
        m = IMPORT_RE.match(s)
        if not m:
            break
        imports.append(m.group(1).replace("«", "").replace("»", ""))
    return imports


def module_title(text: str) -> str | None:
    """The `# Title` heading of the module docstring, if there is one."""
    m = TITLE_RE.search(text)
    return m.group(1).strip() if m else None


def declarations(text: str) -> list[str]:
    """Fully qualified names of the declarations in one file, by `lean_source`'s parser."""
    extra = ((m.start(), m.group("name"))
             for m in EXTRA_DECL_RE.finditer(strip_comments_and_strings(text)))
    return sorted(qualified_declarations(text, extra_declarations=extra))


def opened_namespaces(text: str) -> list[str]:
    """The namespaces a file opens with `open` (local `open ... in` included), whose names can
    then be written unqualified.

    `open scoped X` is left out: it activates `X`'s scoped notation, instances and attributes but
    does not make `X`'s declarations resolvable without the prefix, so it is no resolution
    prefix.
    """
    opened = []
    for line in strip_comments_and_strings(text).splitlines():
        m = OPEN_RE.match(line)
        if not m:
            continue
        rest = re.sub(r"\([^)]*\)", " ", m.group(1))
        rest = re.split(r"\bin\b|\bhiding\b|\brenaming\b", rest)[0]
        words = rest.split()
        if words and words[0] == "scoped":
            continue
        opened.extend(w for w in words if IDENT_RE.fullmatch(w))
    return opened


# --- The library -----------------------------------------------------------------------------

def module_of(path: pathlib.Path, root: pathlib.Path) -> str:
    return ".".join(path.relative_to(root).with_suffix("").parts)


def package_of(module: str) -> str:
    root = module.split(".")[0]
    return PACKAGES.get(root, (root, None))[0]


def read_library(root: pathlib.Path) -> dict[str, dict]:
    """Every module under `root/EpsilonEridani`, with its imports, declarations and metadata."""
    modules = {}
    for path in sorted((root / LIB).rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        name = module_of(path, root)
        decls = declarations(text)
        own = [d for d in decls if d == LIB or d.startswith(LIB + ".")]
        modules[name] = {
            "path": path.relative_to(root).as_posix(),
            "imports": parse_imports(text),
            "decls": decls,
            "lines": text.count("\n") + (0 if text.endswith("\n") else 1),
            "title": module_title(text),
            # Material in an upstream namespace is written to move to PhyslibAlpha as is.
            "upstream_namespace": bool(decls) and not own,
        }
    return modules


def read_manifest(root: pathlib.Path) -> dict[str, dict]:
    path = root / "lake-manifest.json"
    if not path.exists():
        return {}
    return {p["name"]: p for p in json.loads(path.read_text()).get("packages", [])}


def external_url(module: str, manifest: dict[str, dict]) -> str | None:
    """The upstream module's source at the commit the manifest pins."""
    entry = manifest.get(PACKAGES.get(module.split(".")[0], (None, None))[1] or "")
    if not entry or not entry.get("url", "").startswith("https://github.com/"):
        return None
    base = entry["url"].removesuffix(".git")
    sub = (entry.get("subDir") or "").strip("/")
    path = "/".join(filter(None, [sub, module.replace(".", "/") + ".lean"]))
    return f"{base}/blob/{entry['rev']}/{path}"


# --- The roadmaps ----------------------------------------------------------------------------

def layer_sections(text: str) -> list[tuple[str, int, str]]:
    """Split a roadmap file at its `/-! ## ... -/` headings: (title, first line, body)."""
    lines = text.splitlines()
    sections: list[tuple[str, int, list[str]]] = [("Overview", 1, [])]
    i = 0
    while i < len(lines):
        m = LAYER_RE.match(lines[i])
        if m:
            title, start = m.group(1), i + 1
            # A heading may wrap onto further lines; it ends at the comment's close or at a
            # blank line, after which the comment's prose begins.
            while "-/" not in title and i + 1 < len(lines) and lines[i + 1].strip():
                i += 1
                title += " " + lines[i].strip()
            sections.append((title.split("-/")[0].strip(), start, []))
        else:
            sections[-1][2].append(lines[i])
        i += 1
    return [(t, start, "\n".join(body)) for t, start, body in sections
            if t != "Overview" or TARGET_RE.search("\n".join(body))]


def resolve(names: set[str], opens: list[str], index: dict[str, str]) -> dict[str, str]:
    """Map each identifier that names an indexed declaration or module to its full name."""
    prefixes = [""] + [o + "." for o in opens] + [LIB + "."]
    found = {}
    for ident in names:
        parts = ident.split(".")
        # `K.p` or `Foo.bar.mk` may be a field or constructor of an indexed type; fall back to
        # the longest prefix, but never below two components, so a lone local variable does
        # not resolve.
        for k in range(len(parts), 0, -1):
            if k < len(parts) and k < 2:
                break
            stem = ".".join(parts[:k])
            hit = next((p + stem for p in prefixes if p + stem in index), None)
            if hit:
                found[ident] = hit
                break
    return found


def read_roadmaps(roadmap_dir: pathlib.Path, index: dict[str, str],
                  modules: dict[str, dict]) -> list[dict]:
    """One entry per layer section of each roadmap, with the library modules it builds on.

    A layer's id is `roadmap:<Area>#<layer id>`, the layer id being `roadmap_progress.layer_id`
    of the section heading (`Layer 1` for `Layer 1: ...`), so that it names the same layer as the
    Progress page; a heading without a layer lead keeps its whole title. A roadmap file other
    than `Suggested.lean` adds its path: `roadmap:<Area>/<stem>#<layer id>`.
    `uses` maps each module to the names that resolve into it and whether the file imports it.
    """
    # Docstrings name modules as well as declarations (`EpsilonEridani.QFT.Shower.Sudakov`).
    index = {**{m: m for m in modules}, **index}
    layers = []
    for top in ROADMAP_AREAS:
        base = roadmap_dir / top
        if not base.is_dir():
            continue
        for area_dir in sorted(p for p in base.iterdir() if p.is_dir()):
            area = area_dir.name
            for path in sorted(area_dir.rglob("*.lean")):
                raw = path.read_text(encoding="utf-8")
                text = strip_comments_and_strings(raw, keep_docs=True)
                opens = opened_namespaces(raw)
                direct = {m for m in parse_imports(raw) if m in modules}
                rel = path.relative_to(roadmap_dir)
                stem = path.relative_to(area_dir).with_suffix("").as_posix()
                suggested = path.stem == "Suggested"
                file_label = "" if suggested else f"{path.stem}: "
                prefix = f"roadmap:{area}#" if suggested else f"roadmap:{area}/{stem}#"
                seen: collections.Counter[str] = collections.Counter()
                for n, (title, start, body) in enumerate(layer_sections(text)):
                    hits = resolve(set(IDENT_RE.findall(body)), opens, index)
                    names = collections.defaultdict(set)
                    for full in hits.values():
                        names[index[full]].add(full)
                    imported = direct if n == 0 else set()
                    key = layer_id(title)
                    seen[key] += 1
                    if seen[key] > 1:  # two sections under one lead keep distinct nodes
                        key = f"{key} ({seen[key]})"
                    layers.append({
                        "id": prefix + key,
                        "area": area,
                        "completed": top == "Completed",
                        "title": file_label + title,
                        "targets": len(TARGET_RE.findall(body)),
                        "url": f"{ROADMAP_REPO_URL}/blob/main/{rel.as_posix()}#L{start}",
                        "readme": f"{ROADMAP_REPO_URL}/blob/main/{top}/{area}/README.md",
                        "uses": {m: {"names": sorted(names.get(m, ())),
                                     "imported": m in imported}
                                 for m in sorted(set(names) | imported)},
                    })
    return layers


# --- The graph -------------------------------------------------------------------------------

def transitive_reduction(edges: list[tuple[str, str]]) -> set[tuple[str, str]]:
    """The edges implied by others: `u -> v` where `v` stays reachable from `u` without it.

    Edges are dropped one at a time and each check runs on what is left, so reachability is
    always preserved; on a DAG this is the unique transitive reduction.
    """
    succ = collections.defaultdict(set)
    for u, v in edges:
        succ[u].add(v)
    redundant = set()
    for u, v in sorted(edges):
        succ[u].discard(v)
        seen, todo = {u}, [u]
        while todo and v not in seen:
            for w in succ[todo.pop()]:
                if w not in seen:
                    seen.add(w)
                    todo.append(w)
        if v in seen:
            redundant.add((u, v))
        else:
            succ[u].add(v)
    return redundant


def build_graph(root: pathlib.Path, roadmap_dir: pathlib.Path | None) -> dict:
    """The graph published as `module-graph.json`.

    Top level: `generated_at`, `library_commit`, `roadmap_commit` (`null` without roadmaps),
    `package_order` (the order the viewer lists upstream packages in), `style` (the viewer's
    palette, from `chart_style`: `bg`, `panel`, `line`, `text`, `muted`, `sans`, `roadmap`, and
    `dirs`, a colour per top-level library directory), `nodes` and `edges`.

    Every node has `id`, `kind`, `package` and `label`; by kind it also carries
      - `module`, a library module: `dir` (its top-level directory), `title` (the module
        docstring's heading, or `null`), `lines`, `decls` (declaration count),
        `upstream_namespace` (every declaration lies outside the `EpsilonEridani` namespace, so
        the module is PhyslibAlpha-eligible), `url` (source) and `docs` (API docs);
      - `external`, an upstream module the library imports directly: `url` (source at the
        manifest's pin, or `null`) and, for Mathlib, `docs`;
      - `roadmap`, a roadmap layer (see `read_roadmaps`): `area`, `completed`, `targets` (the
        number of suggested declarations), `url` (the section) and `readme`.

    Every edge has `source`, `target` and `kind`, and points downstream:
      - `import`: `target` imports `source`; `redundant` is true when the import is implied by
        the others (see `transitive_reduction`);
      - `roadmap`: layer `target` builds on module `source`; `names` lists the declarations of
        `source` the layer names, and `imported` is true when the roadmap file imports `source`.
    """
    modules = read_library(root)
    manifest = read_manifest(root)
    index = {d: m for m, info in modules.items() for d in info["decls"]}

    nodes, edges = [], []
    for name, info in modules.items():
        parts = name.split(".")
        nodes.append({
            "id": name, "kind": "module", "package": LIB,
            "dir": parts[1] if len(parts) > 2 else "(root)",
            "label": parts[-1], "title": info["title"],
            "lines": info["lines"], "decls": len(info["decls"]),
            "upstream_namespace": info["upstream_namespace"],
            "url": f"{REPO_URL}/blob/main/{info['path']}",
            "docs": f"{DOCS_URL}/{name.replace('.', '/')}.html",
        })

    externals: dict[str, set[str]] = collections.defaultdict(set)
    for name, info in modules.items():
        for target in info["imports"]:
            if target not in modules:
                externals[target].add(name)
            edges.append({"source": target, "target": name, "kind": "import"})
    for ext in sorted(externals):
        pkg = package_of(ext)
        node = {"id": ext, "kind": "external", "package": pkg, "label": ext,
                "url": external_url(ext, manifest)}
        if pkg == "Mathlib":
            node["docs"] = f"{MATHLIB_DOCS_URL}/{ext.replace('.', '/')}.html"
        nodes.append(node)

    redundant = transitive_reduction([(e["source"], e["target"]) for e in edges])
    for e in edges:
        e["redundant"] = (e["source"], e["target"]) in redundant

    layers = read_roadmaps(roadmap_dir, index, modules) if roadmap_dir else []
    for layer in layers:
        nodes.append({"id": layer["id"], "kind": "roadmap", "package": "Roadmaps",
                      "area": layer["area"], "completed": layer["completed"],
                      "label": layer["title"], "targets": layer["targets"],
                      "url": layer["url"], "readme": layer["readme"]})
        for m, use in layer["uses"].items():
            edges.append({"source": m, "target": layer["id"], "kind": "roadmap", **use})

    graph = {
        "generated_at": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "library_commit": git_head(root),
        "roadmap_commit": git_head(roadmap_dir) if roadmap_dir else None,
        "package_order": PACKAGE_ORDER,
        "nodes": nodes,
        "edges": edges,
    }
    graph["style"] = {"bg": BG, "panel": PANEL, "line": BAR_BG, "text": TEXT, "muted": MUTED,
                      "sans": FONT_FAMILY, "roadmap": ROADMAP_COLOR, "dirs": color_map(graph)}
    return graph


# --- Rendering -------------------------------------------------------------------------------

def color_map(graph: dict) -> dict[str, str]:
    """A stable colour per top-level library directory, avoiding the roadmap yellow."""
    dirs = sorted({n["dir"] for n in graph["nodes"] if n["kind"] == "module"})
    palette = [c for c in PALETTE if c != ROADMAP_COLOR]
    return {d: palette[i % len(palette)] for i, d in enumerate(dirs)}


def to_dot(graph: dict) -> str:
    """Graphviz source: clusters per package and per directory, reduced import edges."""
    colors = color_map(graph)
    q = json.dumps
    out = ["digraph EpsilonEridani {",
           f'  graph [rankdir=TB, bgcolor="{BG}", fontcolor="{TEXT}", fontname="Helvetica", '
           'ranksep=1.2, nodesep=0.15, newrank=true];',
           f'  node [shape=box, style="rounded,filled", fontname="Helvetica", fontsize=10, '
           f'fillcolor="{PANEL}", fontcolor="{TEXT}", color="{MUTED}"];',
           f'  edge [color="{MUTED}80", arrowsize=0.5];']
    # A roadmap layer that names no library declaration would only float unattached.
    linked = {e["target"] for e in graph["edges"] if e["kind"] == "roadmap"}
    by_cluster = collections.defaultdict(list)
    for n in graph["nodes"]:
        if n["kind"] == "roadmap" and n["id"] not in linked:
            continue
        key = (n["kind"], n["dir"] if n["kind"] == "module" else n.get("area", n["package"]))
        by_cluster[key].append(n)
    for i, ((kind, group), members) in enumerate(sorted(by_cluster.items())):
        label = {"module": f"{LIB}/{group}", "external": group, "roadmap": f"Roadmap: {group}"}
        out.append(f"  subgraph cluster_{i} {{")
        out.append(f'    label={q(label[kind])}; color="{MUTED}"; style=rounded;')
        for n in members:
            label = ".".join(n["id"].split(".")[-2:]) if kind == "module" else n["label"]
            attrs = {"label": label, "tooltip": n["id"]}
            if n.get("url"):
                attrs["URL"] = n["url"]
            if kind == "module":
                attrs["color"] = colors[group]
                if n["upstream_namespace"]:
                    attrs["style"] = "rounded,filled,dashed"
            elif kind == "external":
                attrs["shape"] = "cds"
            else:
                attrs["shape"] = "note"
            out.append(f"    {q(n['id'])} [" +
                       ", ".join(f"{k}={q(v)}" for k, v in attrs.items()) + "];")
        out.append("  }")
    for e in graph["edges"]:
        if e.get("redundant"):
            continue
        style = f' [style=dashed, color="{ROADMAP_COLOR}80"]' if e["kind"] == "roadmap" else ""
        out.append(f"  {q(e['source'])} -> {q(e['target'])}{style};")
    out.append("}")
    return "\n".join(out) + "\n"


def to_html(graph: dict, static_dir: pathlib.Path) -> str:
    """A local preview: the committed viewer with the data and the site's stylesheet inlined,
    so it opens from `file://`, where the viewer could not fetch `module-graph.json`."""
    viewer = (static_dir / "module-graph.html").read_text(encoding="utf-8")
    css = (static_dir / "style.css").read_text(encoding="utf-8")
    data = json.dumps(graph, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")
    link = '<link rel="stylesheet" href="style.css">'
    if viewer.count(link) != 1:
        raise ValueError(f"expected one {link} in the viewer")
    return viewer.replace(link, f"<style>\n{css}</style>\n"
                                f"<script>window.MODULE_GRAPH = {data};</script>")


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    ap.add_argument("--root", type=pathlib.Path, default=pathlib.Path(__file__).parent.parent,
                    help="the EpsilonEridani checkout (default: this repository)")
    ap.add_argument("--roadmap-dir", type=pathlib.Path,
                    help="an EpsilonEridaniRoadmaps checkout; adds the roadmap target layers")
    ap.add_argument("--out-dir", type=pathlib.Path, default=pathlib.Path("build/module-graph"))
    ap.add_argument("--svg", action="store_true",
                    help="also render module-graph.svg with Graphviz `dot` (must be on PATH)")
    args = ap.parse_args(argv)

    graph = build_graph(args.root.resolve(), args.roadmap_dir)
    args.out_dir.mkdir(parents=True, exist_ok=True)
    (args.out_dir / "module-graph.json").write_text(json.dumps(graph, indent=1) + "\n")
    dot = to_dot(graph)
    (args.out_dir / "module-graph.dot").write_text(dot)
    static_dir = args.root.resolve() / "web" / "static_files"
    (args.out_dir / "module-graph.html").write_text(to_html(graph, static_dir), encoding="utf-8")
    if args.svg:
        subprocess.run(["dot", "-Tsvg", "-o", str(args.out_dir / "module-graph.svg")],
                       input=dot, text=True, check=True)

    kinds = collections.Counter(n["kind"] for n in graph["nodes"])
    reduced = sum(1 for e in graph["edges"] if e.get("redundant"))
    print(f"{kinds['module']} modules, {kinds['external']} entry points, "
          f"{kinds['roadmap']} roadmap layers; {len(graph['edges'])} edges "
          f"({reduced} implied by transitivity) -> {args.out_dir}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
