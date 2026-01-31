/-
Copyright (c) 2024 The RGAT Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RGAT Team
-/
import RgatNaturePaper.Main

/-!
# Riemannian Geometric-Algebra Transformers (RGAT) Verification Library

This library contains the formalization of the core mathematical results presented
in the Nature paper "Riemannian Geometric-Algebra Transformers".

## Main Components
* `Basic.lean`: Definitions of Rotors (`Spin(3)`), Geodesic Distance, and the Heat Kernel.
* `BridgeTheorem.lean`: Formal proof of the Bridge Theorem, linking the geometric
  operator to the Euclidean Gaussian kernel in the tangent space limit.
* `Stability.lean`: Analysis of the softmax stability under geometric perturbations.

## Usage
Build this library using `lake build`.
-/
