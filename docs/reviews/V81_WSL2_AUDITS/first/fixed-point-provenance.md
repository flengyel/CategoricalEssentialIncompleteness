# The section 9 Miller sequence

The fixed manuscript-only inventory covers `3dbbf8e15a7cd2f650564f4fbe6974935fd52826`. The new proof uses the same `rho`, `OracleProgram.numberedEval`, `Rationals.q`, and `IsMiller` as the existing project. The independent check spells out the full quantifiers, real inequality, and indexing at `V46MillerFixedPointChecks.lean:45`. The conclusion is existential. The construction uses classical choice and makes no claim of computability of the sequence.

The finite-dimensional input is harfe's [fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4/tree/93a3eed3364281a9dbf9652bb52356a8db65057c), MIT copyright 2026 harfe. Its complete permission and copyright text appears in each of six files. The original upstream modules elaborate without changes on the repository pins, Lean `v4.35.0-rc2` and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. They were then confined to `CategoricalEssentialIncompleteness.V46.Miller.FixedPoint` with local imports. Their original proof terms are retained, except that final alternative formulations of cube and convex-set Brouwer and one unused import have been removed. No dependency or toolchain pin changed.

| Upstream module | Local suffix of `V46MillerFixedPoint` |
| --- | --- |
| `cubical_sperner_prep` | `SpernerCube` |
| `cubical_sperner` | `CubicalSperner` |
| `apply_cubical_sperner` | `Cube` |
| `convex_homeos` | `ConvexHomeomorphisms` |
| `brouwer` | `Brouwer` |
| `kakutani` | `Kakutani` |

`Certificates` proves the nonempty closed graph, interval fibers, and singleton when the indexed oracle computes a real. Finite certificates are recursively enumerable. The proof tests applicability classically, which suffices for existence. `Intervals` takes the compact image over all names of a point and its interval hull, and proves the same singleton conclusion under the common output hypothesis. The main module pulls the coordinate conditions back along finite-cube inclusion, uses Kakutani on each finite box, and takes a decreasing compact intersection. `exists_isMiller` follows at line 125 from `exists_coordinate_fixedPoint`, the closed graph and interval facts, and `isMiller_of_coordinate_mem`.

All ten modules elaborated against the repository pins with `lean -DwarningAsError=true -o <output> <source>`. The individual strict logs are empty on success. A separate import of both the anonymous checks and the Kakutani source inspected eleven named declarations. The kernel reported exactly `propext`, `Classical.choice`, and `Quot.sound` for each, including the underlying finite-dimensional fixed-point theorem, both singleton theorems, and the final existence theorem. See `fixed-point-axioms.lean` and `fixed-point-axioms.log` in this directory.
