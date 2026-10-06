/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedLifting
public import VaughtConjecture.Knight.CappedLiftingUnique

/-! # Original-cap lifting: common semantic interface

Import this module for identity, composition, lower-domain transport, finite-cover
generation, and the stronger all-caps conclusion under injective restriction.
The historical namespaces and public signatures are retained. No concrete carrier,
receiver, code table or model is imported.

General capped lifting chooses an output for each compatible ambient and cap.
Only a lawful extension with injective restriction gives one output preserving all
compatible caps simultaneously. Neither condition is asserted on original faces.
-/
@[expose] public section

