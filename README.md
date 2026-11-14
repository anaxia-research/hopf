# Deformed Dumont permutations: Lean 4 and Julia checks

Verification code for the paper *Deformed Dumont Permutations, First Letters and Graphical Shi Regions* by Deep Bhattacharjee. The paper answers the question of Poddar, Sawant and Shankar (arXiv:2603.14508) on the sizes of the sets D(2n-1, j) and their refinement by the first letter, and computes the characteristic polynomial and region count of the homogenized graphical Shi arrangement of every graph. All statements are proved in the paper; the code re-checks finite cases.

## Contents

- `lean/DeformedDumont.lean`: 15 theorems in Lean 4 core (no Mathlib), decided by `native_decide`. They compare the transfer (Theorem 2.1), the closed form (Theorem A) and the first-letter recurrence (Theorem B) with direct enumeration for N ≤ 9.
- `julia/DumontCore.jl`, `julia/run_all.jl`: 9425 exact checks of Theorems 2.1, A, B, C, Corollary 4.1, Proposition 5.1 and Corollary 5.3. Output in `julia/run_all.log`.

## Running

```
lean lean/DeformedDumont.lean          # Lean 4.24.0
julia julia/run_all.jl                 # Julia 1.11, about 1 minute
```

## Contact

Deep Bhattacharjee, ORCID [0000-0003-0466-750X](https://orcid.org/0000-0003-0466-750X). GitHub-related contact: egspl@proton.me.
