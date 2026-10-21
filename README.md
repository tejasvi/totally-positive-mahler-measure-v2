# A lower bound for the smallest limit point of the absolute Mahler measure of totally positive algebraic integers

This repository contains the certificate, the two programs that check it, tests of these programs, the programs that
produced the certificate, and a proof in Lean 4 of the lower bounds of the main theorem under one assumption, for the
paper of the same title by Tejasvi Singh Tomar (Zenodo,
[doi:10.5281/zenodo.23539850](https://doi.org/10.5281/zenodo.23539850)). The repository is archived in the record
[doi:10.5281/zenodo.23539851](https://doi.org/10.5281/zenodo.23539851).

## The result

For an algebraic number α of degree n let M(α) be its Mahler measure, with the leading coefficient of the primitive
minimal polynomial included, and let Ω(α) = M(α)^{1/n}. Then log Ω(α) is the absolute logarithmic Weil height of α.
The paper proves that for every ε > 0, all but finitely many totally positive algebraic numbers α satisfy

    log Ω(α) ≥ m₀ − ε,      m₀ = 19152077587359311629/35184372088832000000 = 0.5443347841…

Since e^{m₀} = 1.72346152…, all but finitely many totally positive algebraic numbers have Ω(α) > 1.7234615, and the
smallest limit point ℓ₊ of the values Ω(α) for totally positive algebraic integers α is at least 1.7234615. The previous
lower bound was 1.722069 (V. Flammang, J. Number Theory 151 (2015)). By work of C. J. Smyth (1980), the smallest limit
point is at most 1.7274. Applied to β², the theorem shows that all but finitely many totally real algebraic numbers β
have Weil height h(β) > 0.2721673.

## How the proof works

1. **Auxiliary function with an energy term** (Lemma 2.2 of the paper). Suppose that

       F(x) = log⁺ x − m − Σ_j c_j log|Q_j(x)| − λ (2 U_ν(x) − I(ν))  ≥  0   for all x > 0

   for nonzero integer polynomials Q_j, weights c_j > 0, λ ≥ 0, and a probability measure ν with compact support and
   ν(D(y, r)) ≤ K r for all discs D(y, r) of radius r ≤ 1. Here U_ν(x) = ∫ log|x − y| dν(y) is the logarithmic potential
   of ν and I(ν) = ∫ U_ν dν its logarithmic energy. Resultants bound the sums of log|Q_j| over the conjugates of α. The
   discriminant bounds the energy of the conjugates after smoothing each of them over a small circle. Together they give
   log Ω(α) ≥ m − λ(1 + log(2Kn))/n for every totally positive α of degree n ≥ 1/(2K) that is not a root of a Q_j.
   The inequality F ≥ 0 forces Σ_j c_j deg Q_j + 2λ ≤ 1, and this absorbs the leading coefficients, so the bound holds
   for algebraic numbers, not only for integers.
2. **Certificate.** Nineteen polynomials with exact rational weights: x and eighteen polynomials of Flammang's table.
   The measure ν is ρ/s, where ρ has a continuous piecewise linear density G on 5473 rational nodes in [0, 11.2] with
   rational values, s = ρ(ℝ), and λ = s. The potential and the energy of ρ have closed forms.
   `certificate/FORMAT.md` describes the file and what the checkers verify.
3. **Verification.** Two programs, written separately (see *Checking the certificate*), verify F ≥ 0 on (0, ∞) in ball
   arithmetic, and the strict inequality Σ_j c_j deg Q_j + 2s < 1 as an exact comparison of rationals.
4. **Lean proof.** `lean/` proves the lower bounds for totally positive numbers in Lean 4, under one assumption from
   potential theory (see *Lean proof*).

## Checking the certificate

Both checkers need Python 3 and `python-flint` (tested with Python 3.13.5 and python-flint 0.9.0). They run on Linux,
because both start their worker processes with the `fork` method of `multiprocessing`. With the option `-I`, Python
ignores the user's site-packages, so `python-flint` has to be installed for the interpreter itself, system-wide or in a
virtual environment. `check_independent.py` makes its checks with assert statements and refuses to run under
`python -O`. From the root of the repository, run

    python3 -I checker/check_certificate.py certificate/tp_certificate.json NPROC
    python3 -I checker/check_independent.py certificate/tp_certificate.json NPROC

where `NPROC` is the number of worker processes. A check succeeds if the program exits with status 0. The last lines are

    VERIFIED: log lambda+ >= m = 19152077587359311629/35184372088832000000 = 0.5443347842; Omega >= 1.7234615  (474s)
    INDEPENDENT VERDICT: VERIFIED log lambda+ >= 19152077587359311629/35184372088832000000 0.5443347841764794

The proved bound is the fraction. The decimals in these lines are rounded to the nearest digit shown, and lambda+
stands for ℓ₊.

`check_certificate.py` uses 200-bit balls. It evaluates the potential and the energy by the closed forms of Lemma 3.1 of
the paper, encloses each root of the polynomials in a window, and uses a chord bound with a rigorous upper bound for F''
on the intervals between windows and nodes. `check_independent.py` was written from an earlier formulation of Lemma 2.2
and from the format description, which also gives the closed forms of Lemma 3.1 and the tail bounds of the first
checker. It was written without access to the first checker and shares no code with it. It uses 128-bit balls (192 bits
for the energy), evaluates the potential piece by piece, and bounds F by second-order Taylor expansions at the midpoints
of intervals. On a 96-thread x86-64 server, `check_certificate.py` took 474 seconds with 64 processes and
`check_independent.py` took 18 seconds with 32 processes. The second program needs fewer interval checks, 8,424 versus
28,408. The output of both runs is in `logs/`, and `logs/RUNS.md` records how we produced the logs.

`check_aux.py` makes three short exact checks that the paper refers to:

    python3 -I checker/check_aux.py certificate/tp_certificate.json

It multiplies back the factorizations over ℤ that `check_independent.py` takes from FLINT, computes max G/s for the
constant K = 2 max G/s of the paper, and prints the zero runs of G and the widths of the root windows of the second
checker. Its output is in `logs/check_aux.log`.

## Tests

The folder `tests/` contains three programs that write modified copies of the certificate (49 files in all) and a driver
that runs both checkers on each copy:

    tests/run_all.sh python3 generate
    tests/run_all.sh python3 first NPROC
    tests/run_all.sh python3 second NPROC

The first command writes the modified certificates to `tests/work/` and checks them against
`tests/expected_outputs.sha256`. The other two write one log per check to `tests/logs/first/` and `tests/logs/second/`.
Running the driver replaces the logs in this repository. We produced those logs with the same command for each file,
several files at a time, so their run times are not comparable with each other. The modifications include raising m₀ by
10⁻⁵, 4·10⁻⁶, 3.1·10⁻⁶ and 2·10⁻⁶; multiplying G by 0.99, 0.9999, 1.0001 and 1.01; multiplying the weight of x by 1.001;
setting the weight of each polynomial to zero in turn; replacing x² − 3x + 1 by x² − 3x + 2; weights with Σ_j c_j deg
Q_j + 2s = 1 and = 1 − 10⁻³⁰; an extra polynomial x¹⁰⁰ − 3 with weight 1/200, which violates the degree condition; and
invalid data (a negative G_k, G_N ≠ 0, two nodes swapped). Both checkers accept the certificate with m₀ raised by
2·10⁻⁶, which is below the margin 3·10⁻⁶ of the certificate. They also accept the certificates in which the weight of
Q_3 (4.1·10⁻⁷) or of Q_18 (5.3·10⁻⁸) is set to zero. `check_independent.py` also accepts the certificate whose cut point
x_lo lies inside the support of G, because it chooses its own cut points. All other modified certificates are rejected
by both. `tests/logs/summary.txt` lists the outcome of every check. The checkers do not read the field `audit_note` that
some test files carry; apart from this field, the 49 files are the thirty-nine different certificates counted in the
paper.

## Search programs

The programs in `search/` produced the certificate. They are not part of the proof, and the checkers do not use them.
They need Python 3 with `numpy`, `scipy`, `python-flint`, and `cvxpy` with the solver `clarabel` (used with Python 3.12,
numpy 2.5.4, scipy 1.18.1, cvxpy 1.9.3 and clarabel 0.11.1). The programs read `search/data/` and write to
`search/scratch/`. The only change from the programs we ran is in their paths, which now point to the directory of the
script.

`data/F29.json` lists the thirty polynomials of the linear program: x, the twenty-seven polynomials of Table 1 of
Flammang's paper as reciprocal polynomials x^d U_j(x + 1/x − 2), the quartic x⁴ − 8x³ + 14x² − 7x + 1 and the cubic x³ −
6x² + 5x − 1. `data/flammang2015_tp_Q.json` holds her table as read from the text layer of the version of the article
deposited on HAL (hal-01231484), and `data/flammang2015_table1_image_transcription.json` holds a second reading made
from the page images. The two readings agree.

The certificate comes from several rounds of the same steps; we ship the files of the last two rounds. The
second-to-last round, run from the directory `search/`, is

    python3 -I tp_nodes.py F27 scratch/primalN_a2_dualN_F27.npy 1e-4 12.0 0.004 0.001 0.008 scratch/nodes_a3.npy \
        0.1255 0.21 0.5065 0.566 0.5985 0.609 0.6475 0.674 1.438 2.0275 3.137 7.5225 10.0
    python3 -I tp_primal_nodes.py F27 scratch/nodes_a3.npy a3
    python3 -I tp_dual_fixedN_par.py scratch/primalN_a3.npy F29

where `scratch/primalN_a2_dualN_F27.npy` holds the weights of the previous round's linear program. The last round is

    python3 -I tp_nodes5.py F29 scratch/primalN_a3_dualN_F29.npy scratch/nodes_a5.npy
    python3 -I tp_primal_nodes.py F29 scratch/nodes_a5.npy a5
    python3 -I tp_dual_fixedN_par.py scratch/primalN_a5.npy F29
    python3 -I export_tp.py scratch/primalN_a5.npy scratch/primalN_a5_dualN_F29.npy F29 3e-6 CERT.json

1. `tp_nodes.py` and `tp_nodes5.py` build the nodes: a grid, refined near the roots of the polynomials whose weight in
   the previous round's linear program exceeds a threshold, and near a few further points.
2. `tp_primal_nodes.py` solves the convex program over measures (piecewise linear densities on these nodes, with the
   energy constraint) and writes `scratch/primalN_<tag>.npy`.
3. `tp_dual_fixedN_par.py` fixes the computed measure as the reference measure, solves the linear program for m, the
   weights and λ, and writes `scratch/primalN_<tag>_dualN_F29.npy`.
4. `export_tp.py` converts the solution to exact rationals and subtracts the margin 3·10⁻⁶ from m.

As written, these commands overwrite the files shipped in `scratch/`. To compare, write to other names: the node
programs take the output file as an argument, and the other steps take another tag in place of `a3` or `a5`. The node
steps and the export step reproduce the shipped `scratch/nodes_a3.npy`, `scratch/nodes_a5.npy` and
`certificate/tp_certificate.json` byte for byte. The steps that solve the convex program and the linear program are
numerical and may differ in the last digits. `tp_dual_fixedN_par.py` evaluates log|Q| by Horner's rule in double
precision, which is inaccurate for the polynomials of degree 32 to 38 near x = 1.95 (Section 5 of the paper). This
affects only how close the weights are to optimal, since the checkers verify the certificate as it stands.

`enum_tp.py DMAX R TFAC OUT.json [DMIN]` lists the monic irreducible polynomials of degree DMIN to DMAX with all roots
in [0, R] and trace at most TFAC times the degree, and `tp_screen_par.py PRIMAL.npy OUT.json LIST.json ...` computes ∫
log|Q| dθ for the measure θ saved in PRIMAL.npy and every polynomial Q of the lists. The screens of Section 5 of the
paper used `enum_tp.py` with (DMAX, R, TFAC) = (5, 10, 3), (6, 10, 2.2) and (7, 10, 2.2), the last two with DMIN = DMAX.
For degree 8 they used its parallel version, `enum_tp_par.py 8 10 2.2 OUT.json NPROC 4`. The four lists contain 246,207
polynomials in all. `tp_dual_rootprod.py` is `tp_dual_fixedN_par.py` with log|Q| computed from the roots of Q. `tpc.py`
and `tpsets.py` hold shared numerics and the polynomial sets. `data/F35.json` is F29 with the six further irreducible
factors of Section 5 of the paper.

## Section 5 computations

The folder `analysis/` holds the programs behind the other numbers of Section 5 of the paper, with their output in
`analysis/out/`. Like the search programs, they are not part of the proof. From the root of the repository:

    python3 -I analysis/lp_roots.py analysis/data/polys_table1.json
    python3 -I analysis/lp_roots.py analysis/data/polys_x_and_27.json
    python3 -I analysis/lp_roots.py analysis/data/polys_x_and_27.json analysis/data/weights_flammang_printed.json
    python3 -I analysis/lp_roots.py analysis/data/polys_x_and_27.json analysis/data/weights_flammang_printed.json \
        23:0.000001784 0:0.1974399320

The first two commands give the linear programs without the energy term, for the nineteen polynomials of Table 1 and for
x together with the twenty-seven polynomials of Flammang's table. The last two give the minimum of her auxiliary
function, with the printed weights and with the weight of U_23 read as 0.000001784 (then c_0 = 0.1974399320). The
outputs are `lp_noenergy_table1.out`,
`lp_noenergy_x_and_27.out`, `flammang_printed_weights.out` and `flammang_c23_read_as_1.784e-6.out`.

    python3 -I analysis/lp_energy_roots.py certificate/tp_certificate.json search/data/F29.json roots \
        2.8781306519508358577886530862e-11

solves the linear program with the reference measure of the certificate and log|Q| computed from the roots
(`lp_energy_roots.out`; about 11 minutes). `dualR_a5_F29.log` and `dualR_a5_F35.log` are the output of
`search/tp_dual_rootprod.py scratch/primalN_a5.npy F29` and `... F35`, run from `search/` on a 96-thread server.

    python3 -I analysis/exact_screen.py certificate/tp_certificate.json search/data/F29.json OUT.json 8 LIST.json ...

computes ∫ log|Q| dν for the reference measure ν of the certificate from Lemma 3.1 of the paper, evaluated at the roots
of Q. It does this for the polynomials of the set and for the lists that `enum_tp.py` and `enum_tp_par.py` write with
the parameters given above. The output is `exact_screen.out`.

    python3 -I -B analysis/cmp_screen.py certificate/tp_certificate.json \
        analysis/data/screen_d8_lowest2000.json
    python3 -I analysis/dips_check.py .

The first compares the 2000 lowest values of the degree-8 screen with these values (`cmp_screen.out`). The second
evaluates the auxiliary function of the round before the last near the nineteen extra points of `tp_nodes5.py`
(`dips_check.out`).

## Lean proof

`lean/` contains a proof in Lean 4 with Mathlib of the lower bounds for totally positive numbers stated above, that is,
of Theorem 1.1 of the paper without its upper bound for the smallest limit point, under one hypothesis,
`EnergySmoothing`. Lean `v4.35.0-rc3` and Mathlib commit `c55e6e786f49` are pinned in `lean/lean-toolchain` and
`lean/lake-manifest.json`. The definitions are in `lean/TPMahler/Statement.lean` and `lean/AuxCommon/Basic.lean`, and
the final theorems are in `lean/TPMahler/FinalN.lean`:

```lean
theorem TPMahler.N.tp_main (hE : EnergySmoothing) (_hC : PwLinClosedForm) (ε : ℝ) (hε : 0 < ε) :
    (TPLow (m0 - ε)).Finite
theorem TPMahler.N.tp_omega (hE : EnergySmoothing) (_hC : PwLinClosedForm) :
    {α : ℂ | ∃ P : ℤ[X], IsMinpolyZ P α ∧ AllRootsPos P ∧
      (toC P).mahlerMeasure ^ ((P.natDegree : ℝ)⁻¹) ≤ 17234615 / 10000000}.Finite
theorem TPMahler.N.tp_limit_point (hE : EnergySmoothing) (_hC : PwLinClosedForm) :
    ∀ y : ℝ, AccPt y (𝓟 Lplus) → Real.exp m0 ≤ y
theorem TPMahler.N.exp_m0_gt : (17234615 / 10000000 : ℝ) < Real.exp m0
```

Here `IsMinpolyZ P α` says that P is irreducible in ℤ[X], has positive degree and vanishes at α; `AllRootsPos P` says
that all complex roots of P are real and positive; `TPLow B` is the set of such α with log M(P)/deg P ≤ B; `Lplus` is
the set of the values M(P)^{1/deg P} for totally positive algebraic integers α; and `m0` is m₀ above.

`EnergySmoothing` is the one hypothesis that the proof uses: the smoothing and energy inequality from the proof of
Lemma 2.2, for any n distinct complex numbers (Section 4 of the paper writes it out). `PwLinClosedForm`, the closed
forms of Lemma 3.1, is in the signatures but not used: the proof applies instead the theorem `TPMahler.pwLinClosedForm`,
which proves it.

`TPMahler/Statement.lean` holds the statements of record: the same four theorems, under the same names without `N.`,
with `sorry` in place of the proofs by design, so that the reviewed statements can be read apart from the proofs.
Every build therefore prints four warnings about `sorry`. The proved theorems are `TPMahler.N.tp_main`, `tp_omega`,
`tp_limit_point` and `exp_m0_gt` in `FinalN.lean`. Their types are alpha-equivalent to those of the statements, and
`#print axioms` (see below) shows that none of them depends on `sorry`.

```
cd lean
lake exe cache get                                  # Mathlib for the pinned manifest
lake build TPMahler.FinalN TPMahler.Statement
```

`lean/` is a subset of the Lean project in which the proof was written and checked. It holds the files of the build
above, the root modules of the two core libraries with `TPCore/Lits.lean`, which `TPCore.lean` imports, and in
`lean/tools/` the scripts that wrote the generated files and a diagnostic script. It differs from the project only in
comments and docstrings, from which some internal labels were removed (three of the scripts write these comments into
the files they generate), and in `lakefile.toml`, which no longer declares a library for another paper. The lakefile
still declares a kernel-only variant of the computational part and some benchmarks, whose files are not included; they
are not default targets, so a plain `lake build` also works and builds every module in `lean/`. `lean/SHA256SUMS` lists
the SHA-256 of the files of `lean/`.

A checking program in core Lean (`lean/TPCore/`, with the integer logarithm in `lean/AuxCore/`) verifies the inequality
of the certificate on 8,815 intervals of [2^-30, 21], the two tails, a lower bound for the energy and the condition on
the weights, and `lean/TPMahler/` proves that its acceptance, together with `EnergySmoothing`, implies `tp_main`,
`tp_omega` and `tp_limit_point`. Its checks are evaluated by `native_decide`, which executes compiled code, so the
trusted base includes the Lean compiler, the C compiler that it uses and the Lean runtime. `#print axioms` gives, for
`tp_main`, `tp_omega` and `tp_limit_point`, the standard axioms `propext`, `Classical.choice` and `Quot.sound` plus 47
axioms `TPCore.TPN.….native_decide.ax_1_1`, one for each check: the 43 blocks of intervals in `lean/TPN/Chunk000.lean`
to `Chunk042.lean`, and the energy, the weights and the two tails in `lean/TPN/Globals.lean`. `exp_m0_gt` and
`pwLinClosedForm` use the standard axioms only. `lean/TPN/Globals.lean` also holds a fifth `native_decide` check,
`data_ok`, which the final theorems do not use.

`gen_tp_data.py` writes the certificate data `TPCore/Data.lean`. `tp_roots.py` writes brackets for the real roots of
the polynomials, and from them `tp_check_ref.py`, a Python reimplementation of the leaf checks, computes the tiling.
From the tiling, `gen_tp_leaves.py` writes `TPCore/Leaves.lean`, `gen_tp_lits.py` writes `TPCore/Lits.lean`, and
`gen_tp_shards.py` in mode `N` writes the 43 blocks `TPN/Chunk*.lean`. `tp_diag.py` reports the cost of the tiling per
initial interval. The statements of the theorems do not refer to the generated files, which therefore need not be
trusted.

### Known discrepancies

Some comments and scripts in `lean/` are out of date:

- The module documentation of `TPMahler/Statement.lean` predates the proofs. It calls the file a draft whose proofs are
  pending in `TPMahler.Main`; there is no such module, and the proofs are the theorems `TPMahler.N.*` in `FinalN.lean`.
- Comments in `TPCore/Check.lean` and the docstring of `tools/gen_tp_data.py` refer to a module `TPCore.DataOK`; there
  is no such module. The logarithm tables of `TPCore/Check.lean` are proved correct by `tab_check` and `l2_check` in
  `TPMahler/CheckSound.lean` and by `tabI_check` and `l2I_check` in `TPMahler/EnergySound.lean`, and
  `TPCore/Data.lean` holds only the data of the certificate.
- The module documentation of `TPCore/Check.lean` names the tail checks `leftTailOK` and `rightTailOK`; the functions
  are `leftTailLB` and `rightTailLB`.
- `TPMahler/LeavesN.lean` names `tools/gen_tp_leavesN.py` as its generator, which is not included.
- `TPCore/Lits.lean` and `tools/gen_tp_lits.py` refer to a kernel check in `TPK/Lits.lean`, which belongs to the
  kernel-only variant and is not included; the proved theorems do not use `TPCore/Lits.lean`.
- The docstring of `tools/tp_check_ref.py` calls it an exact reimplementation of `TPCore.Check`; it has no check of the
  left tail or of the energy, and its usage line omits its fourth argument, the file of root brackets.
- The docstring of `tools/gen_tp_shards.py` places `leavesOK_append` in `TPMahler.CheckSound`; it is in
  `TPMahler/CheckSound10.lean`. The current version of this script also writes the line `import TPCore.Lits` at the top
  of each block; the shipped blocks do not have this line.

## Repository layout

- `certificate/`: the certificate `tp_certificate.json` and its description `FORMAT.md`.
- `checker/`: `check_certificate.py`, `check_independent.py` and `check_aux.py`.
- `logs/`: the output of the three programs on the certificate.
- `tests/`: the programs that write the modified certificates, their expected SHA-256, the driver, and the logs.
- `search/`: the programs that produced the certificate, with their input data.
- `analysis/`: the programs and outputs behind the other numbers of Section 5 of the paper.
- `lean/`: the Lean proof (see *Lean proof*), with its own `SHA256SUMS`.
- `paper/`: LaTeX source of the paper.
- `SHA256SUMS`: SHA-256 of all other files.

## License

Copyright 2026 Tejasvi S. Tomar. Code: Apache-2.0 (see `LICENSE`). Paper, certificate and data: CC BY 4.0
(https://creativecommons.org/licenses/by/4.0/).
