/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import EpsilonEridani.Topology.JordanCurve.Basic
public import EpsilonEridani.Topology.JordanCurve.Path
public import EpsilonEridani.Topology.JordanCurve.Separation
public import EpsilonEridani.Topology.JordanCurve.SmallArc
public import EpsilonEridani.Topology.JordanCurve.Subcontinuum

/-!
# Jordan curves

This module re-exports the Jordan-curve API: the predicate `EpsilonEridani.IsJordanCurve` together with
its transfer lemmas (`EpsilonEridani.Topology.JordanCurve.Basic`), the criterion recognizing the range of
a simple closed path as a Jordan curve (`EpsilonEridani.Topology.JordanCurve.Path`), the cutting of a
Jordan curve at one or two of its points (`EpsilonEridani.Topology.JordanCurve.Separation`), the fact that
two nearby points cut off an arc of small diameter (`EpsilonEridani.Topology.JordanCurve.SmallArc`), and
the classification of the compact connected subsets of a curve
(`EpsilonEridani.Topology.JordanCurve.Subcontinuum`). It declares
nothing of its own, and keeps the import path `EpsilonEridani.Topology.JordanCurve` — which named the
basic theory before it moved into the directory — working.
-/
