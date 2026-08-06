# Verification code for *Mixed Triple Metric Dimension of Polyhedral Graphs: Local Forcing and Extremal Families*

This repository contains the computational verification accompanying the paper. Every row of
Table 2 of the paper (Appendix A) is reproduced by a single self-contained program.

## Contents

| File | Description |
|---|---|
| `mtmd_verify.pl` | the verification program (core Perl, no external dependencies) |
| `verify_output.txt` | transcript of a complete run |
| `README.md` | this file |
| `LICENSE` | CC0 1.0 (public domain dedication) |

## Requirements

Core Perl 5 only. No modules beyond the standard distribution, no external libraries, and no
floating-point arithmetic anywhere: all computations use exact integer arithmetic.

## Running

Full run, reproducing every range stated in the paper:

    perl mtmd_verify.pl

Reduced-range smoke test (a few seconds):

    perl mtmd_verify.pl --quick

Single check by name:

    perl mtmd_verify.pl --only=forcing-theorem

List the available checks:

    perl mtmd_verify.pl --list

The program prints a verdict for each check and exits with status 0 if all pass, nonzero
otherwise. A complete run takes under a minute on a desktop machine.

## Method

Each graph is built from its combinatorial definition. All vertex distances are obtained by
breadth-first search, the element list `V(G) ∪ E(G) ∪ F(G)` is built explicitly with each element
stored as its set of incident vertices, and the distance from a vertex to an element is the
minimum distance to an incident vertex.

A candidate set `S` is tested by hashing the code of every element, so that `S` resolves precisely
when no collision occurs. This costs `O(|S| · (|V|+|E|+|F|))` per candidate rather than the
quadratic cost of pairwise comparison, which is what makes the exhaustive searches feasible.
Minimum values are obtained by testing subsets of increasing size and stopping at the first
success, so every reported minimum is a true minimum and not merely an upper bound.

Two further routines supported the analysis rather than the verification: one lists every vertex
separating a fixed pair of elements, and so computes the forced sets `F(G)`; the other reports the
first unresolved pair for a candidate set.

Face lists are certified throughout by Euler's formula `|V| - |E| + |F| = 2` together with the
requirement that every edge lie on exactly two faces, so that the unbounded face is always
counted.

## What is checked

The program is organized as eighteen independent checks, one per row of Table 2 of the paper.
They fall into three kinds.

**Values.** Exhaustive minimisation over all vertex subsets, so that every reported minimum is a
true minimum: the mixed triple metric dimension of the prisms, antiprisms, stacked prisms
`C_n x P_r`, bipyramids and the icosahedron; the face metric dimension and the mixed metric
dimension of the same graphs; and the values of the layered family `L(n,r,sigma)` against the
question posed in the paper.

**Proofs, not only conclusions.** Several checks re-derive the internal steps of a proof rather
than its statement. The case structures of the two lower-bound lemmas are classified subset by
subset and confirmed exhaustive; the closed-form codes behind the upper-bound construction are
recomputed and compared against breadth-first search; every step of the bipyramid theorem and of
the proposition on `dim_m(A_4)` is re-derived independently.

**Structural criteria.** The forcing criterion is tested against a direct separator count over all
triangular edge-face pairs of the families considered, and the deletion criterion of the paper is
compared, vertex by vertex, against a direct test of whether `V(G)` minus that vertex resolves.

## Correspondence with the paper

Each check is named after the claim it verifies, and the names match the rows of Table 2. Running
with `--list` prints the names.

## Licence

Released into the public domain under CC0 1.0. See `LICENSE`.
