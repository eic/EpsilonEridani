#!/usr/bin/env python3
"""Regression tests for the module graph.

Run with:

    python3 scripts/test_module_graph.py
"""

import json
import pathlib
import tempfile
import unittest

import module_graph


HEADER = """/-
Copyright (c) 2026 Someone. All rights reserved.
import Not.A.Real.Import
-/
module

public import Mathlib.Analysis.Normed.Basic
import EpsilonEridani.A
meta import Physlib.Relativity.Basic -- a trailing comment

/-! # The title

import Also.Not.An.Import
-/
"""


class ParseTest(unittest.TestCase):
    def test_imports_stop_at_the_header(self):
        self.assertEqual(module_graph.parse_imports(HEADER), [
            {"module": "Mathlib.Analysis.Normed.Basic", "public": True, "meta": False},
            {"module": "EpsilonEridani.A", "public": False, "meta": False},
            {"module": "Physlib.Relativity.Basic", "public": False, "meta": True},
        ])

    def test_title(self):
        self.assertEqual(module_graph.module_title(HEADER), "The title")

    def test_declarations_track_namespaces(self):
        text = """@[expose] public section
namespace EpsilonEridani.QFT
/-- doc -/
@[simp] theorem foo : True := trivial
noncomputable def Bar.baz := 0
section Inner
private lemma qux : True := trivial
end Inner
instance : Inhabited Nat := ⟨0⟩
instance named : Inhabited Nat := ⟨0⟩
theorem _root_.Lorentz.extra : True := trivial
end EpsilonEridani.QFT
structure Top where
end
"""
        self.assertEqual(module_graph.declarations(text), [
            "EpsilonEridani.QFT.foo", "EpsilonEridani.QFT.Bar.baz", "EpsilonEridani.QFT.qux",
            "EpsilonEridani.QFT.named", "Lorentz.extra", "Top",
        ])

    def test_opened_namespaces(self):
        text = "open A.B C in\nopen scoped Real\nopen D (x y) hiding z\n-- open E\n"
        self.assertEqual(module_graph.opened_namespaces(text), ["A.B", "C", "D"])

    def test_layer_sections(self):
        text = ("preamble\n/-! ## Layer 0: first -/\ndef a := 0\n"
                "/-! ## Layer 1: a heading that\n  wraps -/\ntheorem b : True := trivial\n")
        sections = module_graph.layer_sections(text)
        self.assertEqual([(t, line) for t, line, _ in sections],
                         [("Layer 0: first", 2), ("Layer 1: a heading that wraps", 4)])


class ResolveTest(unittest.TestCase):
    INDEX = {"EpsilonEridani.QFT.DIS.Tensors.FL": "M1", "EpsilonEridani.QFT.DIS.Kin": "M2",
             "EpsilonEridani.QFT.DIS.Kin.p": "M2"}

    def test_through_open_namespaces(self):
        found = module_graph.resolve({"Tensors.FL", "Kin", "x"}, ["EpsilonEridani.QFT.DIS"],
                                     self.INDEX)
        self.assertEqual(found, {"Tensors.FL": "EpsilonEridani.QFT.DIS.Tensors.FL",
                                 "Kin": "EpsilonEridani.QFT.DIS.Kin"})

    def test_field_falls_back_to_its_type_but_not_to_a_variable(self):
        found = module_graph.resolve({"EpsilonEridani.QFT.DIS.Kin.q", "K.p"}, [], self.INDEX)
        self.assertEqual(found, {"EpsilonEridani.QFT.DIS.Kin.q": "EpsilonEridani.QFT.DIS.Kin"})


class ReductionTest(unittest.TestCase):
    def test_dag(self):
        edges = [("a", "b"), ("b", "c"), ("a", "c"), ("c", "d"), ("a", "d")]
        self.assertEqual(module_graph.transitive_reduction(edges), {("a", "c"), ("a", "d")})

    def test_cycle_keeps_reachability(self):
        edges = [("a", "b"), ("b", "a"), ("a", "c"), ("b", "c")]
        redundant = module_graph.transitive_reduction(edges)
        self.assertEqual(len(redundant), 1)
        self.assertTrue(redundant <= {("a", "c"), ("b", "c")})


class BuildTest(unittest.TestCase):
    def test_end_to_end(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp, "lib")
            (root / "EpsilonEridani" / "QFT").mkdir(parents=True)
            (root / "EpsilonEridani" / "QFT" / "A.lean").write_text(
                "module\npublic import Mathlib.Data.Real.Basic\n"
                "namespace EpsilonEridani.QFT\ndef sigma := 0\nend EpsilonEridani.QFT\n")
            (root / "EpsilonEridani" / "QFT" / "B.lean").write_text(
                "module\npublic import EpsilonEridani.QFT.A\n"
                "public import Mathlib.Data.Real.Basic\nnamespace Lorentz\ntheorem ext : True := trivial\nend Lorentz\n")
            (root / "lake-manifest.json").write_text(json.dumps({"packages": [{
                "name": "mathlib", "url": "https://github.com/leanprover-community/mathlib4",
                "rev": "abc", "subDir": None}]}))
            roadmaps = pathlib.Path(tmp, "roadmaps", "EpsilonEridaniRoadmaps", "Area")
            roadmaps.mkdir(parents=True)
            (roadmaps / "Suggested.lean").write_text(
                "import EpsilonEridani\nopen EpsilonEridani.QFT\n"
                "/-! ## Layer 0: uses sigma -/\n/-- Builds on `sigma`. -/\ndef t := sigma\n"
                "/-! ## Layer 1: upstream only -/\ndef u := 1\n")
            graph = module_graph.build_graph(root, pathlib.Path(tmp, "roadmaps"))

        nodes = {n["id"]: n for n in graph["nodes"]}
        self.assertEqual(nodes["Mathlib.Data.Real.Basic"]["url"],
                         "https://github.com/leanprover-community/mathlib4/blob/abc/"
                         "Mathlib/Data/Real/Basic.lean")
        self.assertTrue(nodes["EpsilonEridani.QFT.B"]["upstream_namespace"])
        self.assertFalse(nodes["EpsilonEridani.QFT.A"]["upstream_namespace"])
        self.assertTrue(nodes["EpsilonEridani.QFT.A"]["used_by_roadmaps"])
        edges = {(e["source"], e["target"]): e for e in graph["edges"]}
        self.assertTrue(edges[("Mathlib.Data.Real.Basic", "EpsilonEridani.QFT.B")]["redundant"])
        self.assertFalse(edges[("EpsilonEridani.QFT.A", "EpsilonEridani.QFT.B")]["redundant"])
        self.assertEqual(edges[("EpsilonEridani.QFT.A", "roadmap:Area/Suggested#0")]["names"],
                         ["EpsilonEridani.QFT.sigma"])
        self.assertFalse(any(e["target"] == "roadmap:Area/Suggested#1" for e in graph["edges"]))
        self.assertIn("Layer 0: uses sigma", module_graph.to_dot(graph))
        self.assertNotIn("Layer 1: upstream only", module_graph.to_dot(graph))
        self.assertIn('"EpsilonEridani.QFT.A"', module_graph.to_html(graph))


if __name__ == "__main__":
    unittest.main()
