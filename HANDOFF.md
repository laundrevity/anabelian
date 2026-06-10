# HANDOFF.md — session bootstrap (written after Pass 35, 2026-06-10)

You are picking up the `anabelian` project mid-stride. Read in this order before any work:
`CLAUDE.md` (the constitution — axiom budget, rule-2, commit-per-pass), `AXIOM_LEDGER.md`
(state: **0 FOUNDATIONAL / 0 DEBT**, zero `axiom` declarations project-wide — keep it that
way), `ROADMAP.md` (status header says Pass 35), and the **tail of `NOTES.md`** (Passes 29–35:
the descent block, including the complete plan for your first task). Session start: `git
status` must be clean (only `.claude/` untracked is OK) — explain anything else before working.

## Where the mathematics stands

Passes 23–28 built the ramification filtration's finite-level theory abstractly
(hypothesis-parametrized): filtration + basics, tame character `θ₀`, tame injectivity, additive
characters `θ_i`, wild/tame dichotomy (`G₁` a `p`-group, `p ∤ |G₀/G₁|`), plus constructed
witnesses for both regimes. Passes 29–35 (the **descent**) instantiated it on actual local
fields: for finite separable `L/K` (`K` nonarchimedean local), `𝒪_L = extensionIntegers K L` is
a `ValuationSubring` (P29), a DVR with uniformizer package (P30), finite residue field + `CharP`
(P31); the monogenicity engine (P32, Nakayama replaces completeness), its data (P33: `he`
unconditional, `hres` = residue surjectivity; showcase `ker θ₀ = G₁` totally-ramified), the
general-case reduction via `inertiaFixedIntegers` (P34: `ker θ₀ = G₁` for ANY `L/K` modulo one
lemma `hresid`), and the orbit-polynomial bricks for `hresid` (P35).

## YOUR FIRST TASK — Pass 36, the descent finale: prove `hresid`

**Goal:** `hresid : ∀ x : ↥(extensionIntegers K L), ∃ a ∈ inertiaFixedIntegers K L,
x - a ∈ maximalIdeal _` — then the unconditional kernel theorem
(`ker_tameCharacter_extensionIntegers_general` := P34's `ker_tameCharacter_of_inertiaFixed_cover`
+ `hresid`). New file(s) `Anabelian/InertiaResidueCover.lean` (+ a second file if the window
demands; see budget below). **≤ 2 substantial declarations per file.**

**The assembly plan** (elementary — no Hensel, no Lucas, no completeness; bricks from P35's
`Anabelian/InertiaCharpoly.lean`):

1. Let `F := (inertiaFixedIntegers K L).map (residue _)`-image (work with membership, or the
   `Subring.map` of the residue hom). `F` is a finite subring of the finite field `𝓀_L`
   (P31's `finite_residueField_extensionIntegers`), hence a **subfield** (finite integral
   domain is a field); in particular `(m : 𝓀_L) ∈ F` and is invertible in `F` when
   `(m : 𝓀_L) ≠ 0`.
2. For `b : 𝒪_L` with residue `b̄`: P35 gives — every coefficient of `(X − C b̄)^n`,
   `n := Fintype.card ↥G₀`, is in `F` (combine `coeff_inertiaCharpoly_mem` with
   `map_residue_inertiaCharpoly` via `Polynomial.coeff_map`).
3. Write `n = p^a * m` with `p ∤ m` (`p` := the residue characteristic; `n ≠ 0` since `G₀`
   nonempty; `Nat.ord_compl`/`ord_proj` or `Nat.maxPowDiv` machinery — probe). In `𝓀_L[X]`:
   `(X − C b̄)^(p^a * m) = (X^(p^a) − C (b̄^(p^a)))^m` via `sub_pow_char_pow` (CharP of the
   polynomial ring — probe the instance) + `pow_mul`. The coefficient at degree `p^a * (m−1)`
   of the right side is `(m : 𝓀_L) * b̄^(p^a)` up to sign: expand with
   `sub_pow`/`Commute.add_pow`-style binomial sum; only the `j = m−1` term has that degree
   (`Finset.sum_eq_single`, degrees `p^a * j` injective in `j`). Conclude
   `(m : 𝓀_L) * b̄^(p^a) ∈ F` (sign via `neg_mem`).
4. `(m : 𝓀_L) ≠ 0` by `CharP.cast_ne_zero`-style (`p ∤ m`; `CharP 𝓀_L p` from P31's
   `charP_residueField_extensionIntegers`; `p` prime via `𝓀[K]`'s finite-field `CharP` — probe
   how LocalField.Basic exposes the residue characteristic). So `b̄^(p^a) ∈ F` (step 1's
   inverse).
5. Choose `b̄` a **generator of the cyclic `𝓀_Lˣ`** (`IsCyclic` for finite-field units; lift to
   `b` via `Ideal.Quotient.mk_surjective`). `b̄^(p^a)` is also a generator: `p^a` is coprime to
   `orderOf b̄ = |𝓀_Lˣ| = q − 1` (`q` a `p`-power; probe `orderOf_pow_of_coprime`-type name, or
   argue via the Frobenius automorphism). Generators' powers + `0` exhaust `𝓀_L` ⟹ `F = 𝓀_L`
   pointwise ⟹ for any `x`, `residue x ∈ F` ⟹ unpack to `a ∈ inertiaFixedIntegers` with
   `residue a = residue x` ⟹ `x − a ∈ 𝔪` (`Ideal.Quotient.mk_eq_mk_iff_sub_mem`, term-mode —
   the `residue`-vs-`mk` defeq friction is known, see idioms).
6. Edge cases: `b̄ = 0`/`x` arbitrary handled by `F = 𝓀_L` as sets; `G₀` trivial makes
   everything easy but needs no special-casing (`n = 1 = p^0·1`).

Then the one-liner finale theorem, root import in `Anabelian.lean`, audits, governance entries
(ledger + NOTES in the established per-pass format + ROADMAP), commit `pass 36`.

## Environment recipe (Cowork sandbox; all verified this session — details in NOTES P25/P30/P31)

- **Toolchain**: `lean-4.30.0-linux_aarch64.tar.zst` sits in the repo folder (gitignored).
  Extract to the session tmp dir (`$TMPDIR`, persistent across calls): `zstd -d` then `tar -x`
  (two calls). Delete `lib/**/*.a` and the two LLVM `.so`s (~600 MB; not needed for olean
  builds). Disk: session volume is ~10 GB; the workspace copy needs ~6.2 GB.
- **Never `lake build` against the mounted repo**: the FUSE daemon caps ~1019 open files; Lean
  needs ~2000. Build in a **hybrid workspace** under tmp: real dirs; *symlink* repo sources
  (`Anabelian/`, `Anabelian.lean`, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`) and
  each package's source entries; *copy* every `.lake/packages/*/.lake` build tree + the
  project's `.lake/build` (rsync in ~30 s chunks; resumable).
- **45 s hard wall per bash call**; background processes die with the call; ~30 s of every
  build call is olean-loading I/O (closure > RAM). Hence: ≤2 substantial declarations per new
  file; `--log-level=warning` on all builds; expect window variance (a file may build at 33 s
  or time out — just retry); `lake build <Target>` then check the `.olean` exists.
- **Sync back**: `rsync -au ws/.lake/build/ mount/.lake/build/` (update-only — plain `-a` once
  clobbered host artifacts), then `rm -rf mount/.lake/config/*` (machine-pathed; hosts
  reconfigure silently).
- **`GaloisInertia.lean` exceeds the window** — never edit it in-sandbox without host
  verification.
- **git**: set repo-local user from `git log` before committing; push fails in-sandbox (no
  credentials) — the user pushes from the host. Commit every pass.

## House idioms and known traps (hard-won; respect them)

- **Probe before writing**: grep `.lake/packages/mathlib` for every lemma name and SIGNATURE;
  the pin is newer than training priors. Known renames hit so far: `subgroup_units_cyclic →
  isCyclic_subgroup_units`, `isCyclic_of_subgroup_isDomain → isCyclic_of_injective_ringHom`,
  `Irreducible.not_unit → Irreducible.not_isUnit`. `#synth` probe files via `lake env lean`
  resolve instance mysteries (e.g. `Algebra k k⸨X⸩` is `HahnSeries.powerSeriesAlgebra`).
- `residue` vs `Ideal.Quotient.mk`: bridge in TERM MODE (`(Ideal.Quotient.mk_eq_mk_iff_sub_mem
  _ _).mp h` typechecks by defeq; `rw` often fails). `Units.map`-unpacking: `have h1 :
  Units.map ... = 1 := hσ` (defeq), then `congrArg Units.val` + `simpa`.
- `Algebra.smul_def` is NOT `rfl` on subalgebra subtypes (rewrite explicitly via
  `SetLike.val_smul`); it IS `rfl` for `RingHom.toAlgebra`-instances.
- Dependent-motive inductions (`Subring.closure_induction`, `Submodule.span_induction`):
  `clear` duplicate hypotheses about the inducted element first, or IHs become implications.
- Style: `change` not goal-changing `show`; `set_option ... in` + reason comment per
  declaration (before the docstring); ≤100-char lines; audit block `#print axioms` at file end.
- Pass ritual (see any P29–35 NOTES entry): restatement (i)–(iv) → probes → build →
  expectation-vs-reality table → ledger/NOTES/ROADMAP → commit. Honesty sections name what is
  NOT claimed. Never `sorry`, never a new `axiom`, scope-cut stretch goals rather than sink
  passes (P27's twist precedent).

## After Pass 36

The queue (ROADMAP "Honest next step"): P27/P28 instantiations at `𝒪_L` (near-one-liners,
consolidation); the `IsNonarchimedeanLocalField L` instance assembly; then the **ascent**
(Herbrand `φ`/`ψ`, upper numbering — Serre IV §3) toward the absolute-group statements. R1–R3
remain distant targets that must be earned, never axiomatized — the line between inputs and
targets is drawn in `ROADMAP.md` and is the project's reason for existing.
