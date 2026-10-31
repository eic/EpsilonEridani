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
  roadmap's `Suggested.lean` in EpsilonEridaniRoadmaps. Those files import the empty
  `EpsilonEridani` root, so their imports say nothing; an edge `M -> layer` instead means a
  signature or docstring in that section names a declaration that module `M` defines. Names are
  resolved textually against a declaration index built from the sources (tracking `namespace`
  blocks and the section's `open`s), not by Lean, so it is a best-effort reading: a name the
  index misses (a structure field, an auto-generated lemma) draws no edge.

Everything is read from source text, so no build is needed and the Pages workflow can run it
alongside the other chart generators. Outputs, into `--out-dir`:

* `module-graph.json`: the nodes and edges, the data the other two are rendered from;
* `module-graph.dot`: Graphviz source, one cluster per package and per top-level directory, with
  import edges implied by transitivity left out;
* `module-graph.html`: a self-contained interactive viewer (the JSON is inlined, so it opens from
  `file://`) with search, collapsing by directory depth and package, and upstream/downstream
  highlighting.

Pure stdlib, like the other generators, so CI needs no pip install. The viewer loads cytoscape.js
and dagre from a CDN.
"""

from __future__ import annotations

import argparse
import collections
import datetime as dt
import html
import json
import pathlib
import re
import subprocess
import sys

from chart_style import BG, MUTED, PALETTE, PANEL, TEXT

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

IMPORT_RE = re.compile(r"^(public\s+|private\s+)?(meta\s+)?import\s+(all\s+)?([\w.'«»]+)\s*$")
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|public|meta|scoped)\s+)*"
    r"(def|theorem|lemma|abbrev|structure|class(?:\s+inductive)?|inductive|instance|opaque|"
    r"axiom|irreducible_def|notation|macro|elab|syntax)\b"
    r"(?:\s*\([^)]*\))?\s+([^\s:({\[⦃]+)")
NAMESPACE_RE = re.compile(r"^\s*namespace\s+(\S+)")
SECTION_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|public|private)\s+)*section\b(?:\s+(\S+))?")
END_RE = re.compile(r"^\s*end\b(?:\s+(\S+))?\s*$")
OPEN_RE = re.compile(r"^\s*open\s+(.*)$")
LAYER_RE = re.compile(r"^/-!\s*##\s+(.*)$")
TITLE_RE = re.compile(r"/-!\s*\n?\s*#\s+(.+)")
IDENT_RE = re.compile(r"[\w'!?]+(?:\.[\w'!?]+)*")
TARGET_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*"
                       r"(def|theorem|lemma|abbrev|structure|class|inductive|instance)\b", re.M)


# --- Lean source handling --------------------------------------------------------------------

def strip_comments(text: str, keep_docs: bool = False) -> str:
    """Blank out comments, keeping every newline so line numbers survive.

    Block comments nest in Lean. With `keep_docs`, doc comments (`/--`, `/-!`) are kept, since
    a roadmap's docstrings name the upstream declarations a target builds on.
    """
    out = []
    i, n, depth, keep = 0, len(text), 0, False
    in_string = False
    while i < n:
        c = text[i]
        if depth == 0:
            if in_string:
                out.append(c)
                if c == "\\" and i + 1 < n:
                    out.append(text[i + 1])
                    i += 2
                    continue
                if c == '"':
                    in_string = False
                i += 1
                continue
            if c == '"':
                in_string = True
                out.append(c)
                i += 1
                continue
            if text.startswith("--", i):
                j = text.find("\n", i)
                j = n if j < 0 else j
                i = j
                continue
            if text.startswith("/-", i):
                depth = 1
                keep = keep_docs and i + 2 < n and text[i + 2] in "-!"
                out.append(text[i:i + 2] if keep else "  ")
                i += 2
                continue
            out.append(c)
            i += 1
            continue
        if text.startswith("/-", i):
            depth += 1
            out.append(text[i:i + 2] if keep else "  ")
            i += 2
        elif text.startswith("-/", i):
            depth -= 1
            out.append(text[i:i + 2] if keep else "  ")
            i += 2
        else:
            out.append(c if keep or c == "\n" else " ")
            i += 1
    return "".join(out)


def parse_imports(text: str) -> list[dict]:
    """The header imports of a Lean file, each with whether it is `public` and/or `meta`."""
    imports = []
    for line in strip_comments(text).splitlines():
        s = line.strip()
        if not s or s in ("module", "prelude"):
            continue
        m = IMPORT_RE.match(s)
        if not m:
            break
        imports.append({"module": m.group(4).replace("«", "").replace("»", ""),
                        "public": bool(m.group(1) and m.group(1).startswith("public")),
                        "meta": bool(m.group(2))})
    return imports


def module_title(text: str) -> str | None:
    """The `# Title` heading of the module docstring, if there is one."""
    m = TITLE_RE.search(text)
    return m.group(1).strip() if m else None


def declarations(text: str) -> list[str]:
    """Fully qualified names of the declarations in one file, tracking `namespace` blocks.

    A textual approximation: it sees the declaration keywords at the start of a line and the
    `namespace`/`section`/`end` structure, which is all a name lookup needs.
    """
    stack: list[list[str]] = []
    names = []
    for line in strip_comments(text).splitlines():
        if m := NAMESPACE_RE.match(line):
            stack.append(m.group(1).split("."))
            continue
        if SECTION_RE.match(line):
            stack.append([])
            continue
        if m := END_RE.match(line):
            if stack:
                stack.pop()
            continue
        m = DECL_RE.match(line)
        if not m or m.group(1) in ("notation", "macro", "elab", "syntax"):
            continue
        name = m.group(2)
        if name.startswith("_root_."):
            names.append(name[len("_root_."):])
        else:
            names.append(".".join([p for frame in stack for p in frame] + [name]))
    return names


def opened_namespaces(text: str) -> list[str]:
    """Every namespace a file brings into scope with `open` (local `open ... in` included)."""
    opened = []
    for line in strip_comments(text).splitlines():
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
            "path": str(path.relative_to(root)),
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
            while "-/" not in title and i + 1 < len(lines):
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
    """One entry per layer section of each roadmap, with the library modules it builds on."""
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
                text = strip_comments(raw, keep_docs=True)
                opens = opened_namespaces(raw)
                direct = [i["module"] for i in parse_imports(raw) if i["module"] in modules]
                rel = path.relative_to(roadmap_dir)
                stem = path.relative_to(area_dir).with_suffix("").as_posix()
                file_label = "" if path.stem == "Suggested" else f"{path.stem}: "
                for n, (title, start, body) in enumerate(layer_sections(text)):
                    hits = resolve(set(IDENT_RE.findall(body)), opens, index)
                    uses = collections.defaultdict(set)
                    for full in hits.values():
                        uses[index[full]].add(full)
                    for m in direct if n == 0 else []:
                        uses[m]
                    layers.append({
                        "id": f"roadmap:{area}/{stem}#{n}",
                        "area": area,
                        "completed": top == "Completed",
                        "title": file_label + title,
                        "targets": len(TARGET_RE.findall(body)),
                        "url": f"{ROADMAP_REPO_URL}/blob/main/{rel.as_posix()}#L{start}",
                        "readme": f"{ROADMAP_REPO_URL}/blob/main/{top}/{area}/README.md",
                        "uses": {m: sorted(v) for m, v in sorted(uses.items())},
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


def git_head(root: pathlib.Path) -> str | None:
    try:
        return subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"], check=True,
                              capture_output=True, text=True).stdout.strip() or None
    except (OSError, subprocess.CalledProcessError):
        return None


def build_graph(root: pathlib.Path, roadmap_dir: pathlib.Path | None) -> dict:
    modules = read_library(root)
    manifest = read_manifest(root)
    index = {d: m for m, info in modules.items() for d in info["decls"]}

    nodes, edges = [], []
    for name, info in modules.items():
        parts = name.split(".")
        nodes.append({
            "id": name, "kind": "module", "package": LIB,
            "dir": parts[1] if len(parts) > 2 else "(root)",
            "label": parts[-1], "title": info["title"], "path": info["path"],
            "lines": info["lines"], "decls": len(info["decls"]),
            "upstream_namespace": info["upstream_namespace"],
            "url": f"{REPO_URL}/blob/main/{info['path']}",
            "docs": f"{DOCS_URL}/{name.replace('.', '/')}.html",
        })

    externals: dict[str, set[str]] = collections.defaultdict(set)
    for name, info in modules.items():
        for imp in info["imports"]:
            target = imp["module"]
            if target not in modules:
                externals[target].add(name)
            edges.append({"source": target, "target": name, "kind": "import",
                          "public": imp["public"], "meta": imp["meta"]})
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
        for m, names in layer["uses"].items():
            edges.append({"source": m, "target": layer["id"], "kind": "roadmap",
                          "names": names})

    used = {e["source"] for e in edges if e["kind"] == "roadmap"}
    for node in nodes:
        if node["kind"] == "module":
            node["used_by_roadmaps"] = node["id"] in used

    manifest_revs = {PACKAGES[r][0]: manifest[PACKAGES[r][1]]["rev"]
                     for r in PACKAGES if PACKAGES[r][1] in manifest}
    return {
        "generated_at": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "library_commit": git_head(root),
        "roadmap_commit": git_head(roadmap_dir) if roadmap_dir else None,
        "pins": manifest_revs,
        "package_order": PACKAGE_ORDER,
        "nodes": nodes,
        "edges": edges,
    }


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


def to_html(graph: dict, home: str | None = None) -> str:
    template = (pathlib.Path(__file__).parent / "module_graph.html").read_text(encoding="utf-8")
    data = json.dumps(graph, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")
    style = {"bg": BG, "panel": PANEL, "text": TEXT, "muted": MUTED, "palette": PALETTE,
             "dirs": color_map(graph)}
    return (template.replace("/*GRAPH_DATA*/null", data)
            .replace("/*STYLE_DATA*/null", json.dumps(style))
            .replace("{{HOME}}", f'<a class="home" href="{html.escape(home)}">← Site</a>'
                     if home else "")
            .replace("{{LIB}}", html.escape(LIB)))


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    ap.add_argument("--root", type=pathlib.Path, default=pathlib.Path(__file__).parent.parent,
                    help="the EpsilonEridani checkout (default: this repository)")
    ap.add_argument("--roadmap-dir", type=pathlib.Path,
                    help="an EpsilonEridaniRoadmaps checkout; adds the roadmap target layers")
    ap.add_argument("--out-dir", type=pathlib.Path, default=pathlib.Path("build/module-graph"))
    ap.add_argument("--home", help="a link back to the site, shown in the viewer's header")
    ap.add_argument("--svg", action="store_true",
                    help="also render module-graph.svg with Graphviz `dot` (must be on PATH)")
    args = ap.parse_args(argv)

    graph = build_graph(args.root.resolve(), args.roadmap_dir)
    args.out_dir.mkdir(parents=True, exist_ok=True)
    (args.out_dir / "module-graph.json").write_text(json.dumps(graph, indent=1) + "\n")
    dot = to_dot(graph)
    (args.out_dir / "module-graph.dot").write_text(dot)
    (args.out_dir / "module-graph.html").write_text(to_html(graph, args.home),
                                                    encoding="utf-8")
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
