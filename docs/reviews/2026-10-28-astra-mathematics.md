# Independent mathematical review — 28 October 2026

Reviewer: GPT-6 Astra (`gpt-6-astra`), acting as an independent AI review pass. This is not external human peer review or formal certification.

Reviewed baseline: `e7fa570ec7190d7a1c1f3a7c08ee91bc476fdc29` in `Quantyra/corrupted-field-recovery`. All line references below refer to that baseline.

Reviewed files:

- `manuscript/main.tex`, SHA-256 `70A603D9498F7CAFF661364B75E6644102ECD070E4A0F0F9D649EBD9FBDBA400`.
- `src/recovery.py`, SHA-256 `0C54EC4E33BB02E3EDA054A2EFB3360B8C537468BE28AB09836E360617BF5617`.

The required planning README, protocol, research handoff, and S001 story were read for scope. Their correctness assessments were not used as evidence. In particular, this reviewer did not read or rely on `docs/internal-audit.md`. The user's latest instruction permits a DOI-bearing preprint before complete Lean certification and supersedes the older planning dependency.

## Recommendation

The mathematical argument is suitable for publication as an accurately labeled preprint with incomplete formal certification. I found no proved mathematical error or publication-blocking mathematical gap in the reviewed theorem, algorithm, probability bound, or conservative headline resource bounds. The explicit statement that the main theorem and Python implementation are not fully formally verified must remain. This recommendation is a review judgment, not a proof of correctness or novelty.

The release-status wording at the end of the baseline manuscript should be updated for the actual release and the user's revised sequencing. The other suggestions below are optional clarifications, not conditions on publication.

## Findings and requested corrections

### A1. Stale publication dependency — low severity, editorial

**Location:** `manuscript/main.tex:413–414`, and the working-draft date at line 18 when preparing the release version.

**Finding:** The sentence “Release remains pending full validation and Lean certification” states an outdated project decision. It conflicts with the current instruction to publish a correctly labeled preprint before complete Lean certification. It is not a mathematical error.

**Correction:** Describe the actual release status and continuing formalization work. Update DOI wording only when a DOI has actually been assigned and verified. Preserve the distinction between an exact output certificate and complete Lean certification.

**Blocks publication?** No mathematical blocker. Correct this metadata in the release preparation; do not interpret it as a requirement to finish Lean first.

### A2. Specify dual injectivity directly — low severity, editorial

**Location:** `manuscript/main.tex:150–153`.

**Finding:** “T invertible on U” is awkward because T acts on V, whereas U is a subspace of V*. The following qualification, `dim T*U = dim U`, supplies the correct condition, so the present lemma is mathematically unambiguous when read in full.

**Correction:** Prefer “the restriction of T* to U is injective” together with `U ∩ T*U = {0}`. No change to the hypothesis or proof is required.

**Blocks publication?** No.

### A3. Separate abstract stage costs from Python packing costs — low severity, clarification

**Location:** `manuscript/main.tex:303–321`; `src/recovery.py:250–261`.

**Finding:** The O(n^6) exterior-column construction count is valid for direct writes into explicit bit arrays. The Python implementation builds packed integers with repeated shifts and OR operations. Those operations can touch an increasing O(n^3)-bit integer, so its literal packed construction should not be read as an O(n^6) bit-time implementation. A direct conservative upper bound for that construction is O(n^9), still comfortably below the stated soft-O(n^12) per-trial envelope. The manuscript already allows interpreter/representation overhead, so this does not contradict the headline theorem.

**Correction:** Optionally add that the displayed stage counts describe elementary bit-array algorithms and that the Python packed-integer implementation is covered by the looser final envelope. Do not advertise the stage counts as measured or verified Python scaling.

**Blocks publication?** No. No change to the headline time or space bounds is indicated by this review.

## Independent reconstruction of the main arguments

### Four contractions

At `manuscript/main.tex:96–130`, preserving the three radicals forces a balanced binary endomorphism to be block diagonal on the three K-lines. The adjoint relations yield A1=A2=A3=A and A=A*. For a weight a in the fourth contraction, balancing is `A* M_a = M_a A`; self-adjointness reduces this to commutation. Commutation with one field generator gives commutation with every element of K, hence K-linearity on a one-dimensional K-space. Conversely, scalar multiplications balance every contraction.

There is no assumption that an arbitrary balance space is an algebra: the proof identifies it with the field only on the good event. Outside that event the algorithm tests powers, a polynomial relation, and irreducibility before constructing a candidate field. This distinction is correct.

I checked the concern that `common_balance` omits diagonal matrix equations. For symmetric binary B, `(T^t B)ii = (B T)ii` identically, so those omitted equations impose no condition. The off-diagonal equations in the implementation have the correct column-major indices.

### Two translates

At `manuscript/main.tex:149–165`, independence of the 2r covectors makes `(u,u∘T)` onto. The selected a with `u(a)=0` and `u(Ta)=u(x)` exactly reproduces E(x,y,·) as a third-mode contraction of the defect. The other containment follows because both summands of each defect contraction lie in W(E). This works when U is a nonminimal support and when E=0.

The defect need not be alternating in all three arguments. This does not invalidate the proof or implementation: W is expressly the third-mode image, and D_T C is symmetric and alternating in its first two arguments. Thus the implementation's use of only i<j to span its third-mode covectors is justified. No third-argument alternation is assumed there.

### Conditional probability and amplification

At `manuscript/main.tex:175–235`, conditioning all four independent physical draws to lie in A gives four independent uniform draws from A. The origin, line, and plane bounds are conditional bounds at successive successful stages, so their union bound does not assume an unconditioned uniform K-coordinate distribution. After a successful basis triple is fixed, a coordinate fiber of the fourth vector has size at most q^2, which gives the claimed non-generator bound.

The correct balance space's ordered binary basis is a deterministic function of the contraction vectors. The independent scalar-index bits consequently give a uniform t in K even when that basis depends on the quadruple. Drawing those bits at the start of the trial instead of after the solve has the same joint distribution.

The bad-position count correctly includes failure of injectivity at t=0: a nonzero pair `(u0,u1)` with `u0+t u1=0` captures both intersections and collapsed translated vectors. If u1 is nonzero, any nonzero K-coordinate gives at most one root. Counting all `2^(2r)-1` pairs overcounts rather than undercounts, as needed.

For `s≥2R+5`, the stated estimates imply beta<1/2 and gamma≥1/4, giving per-trial success at least `2^(-4R-3)`. All trials use fresh bits; `(1-p)^N≤exp(-pN)≤exp(-h)≤2^(-h)` is valid. Earlier acceptance of an alternative verified representation does not compromise the lower bound.

### Coefficient fit and nonzero output

At `manuscript/main.tex:269–294`, an irreducible degree-s relation together with independent powers produces a genuine degree-s field action. The new module basis is related to the planted K-basis by an invertible K-linear change after identifying the two finite fields. Its determinant rescales the coefficient by a nonzero element; field isomorphisms preserve trace. Hence the planted compatible tensor is in the constructed s-column family.

For any nonzero physical vector z, some x,y give a nonzero determinant, and a scalar multiple can make its trace pairing nonzero. Thus a nonzero trace-determinant form has zero radical and full third-mode image V*. The difference of two compatible columns with distinct coefficients is another nonzero trace-determinant form, so it cannot lie in the tensor space supported on a proper U. The coefficient fit therefore cannot choose a zero compatible coefficient on the good event. This argument establishes uniqueness of the compatible component within the recovered coordinates and support; it does not establish uniqueness of a planted representation, and the manuscript does not claim that.

The exact verifier rechecks the field polynomial, coordinate isomorphism, nonzero coefficient, independent support covectors, ranges, and all increasing physical triples. Equality on those triples proves equality of the two alternating trilinear tensors. It does not require trusting any clean-contraction event.

### Computational model

The input size is explicitly Theta(n^3) binary coefficients. Field arithmetic, trace computation, the n^2-variable balance system, polynomial irreducibility test, module construction, defect image, and O(n^3)-by-O(n^3) coefficient system all have polynomial deterministic implementations. No finite-field table, search through q elements, factoring oracle, or uncharged point-count oracle is needed.

The Python loops use polynomial-size packed values and a fixed number of candidates. Witness masks in `span` are also polynomial-sized, including when its input is the streamed family of O(n^2) defect slices. Direct conservative charging of these representations fits the stated time and memory envelopes. The bounded-trial counter and fixed rejection counters require O(R+log(h+1)) bits, not O(N) storage. The implementation draws exactly 4n+s bits per attempted trial; seeded pseudorandom tapes used for tests are appropriately distinguished from the theorem's independent fair-bit model.

## Checks actually executed

Environment: Windows PowerShell; Python 3.13.7 at `C:/Users/dfred/QuantyraTools/SpaceProofs/python/python.exe`. The default `python` command was a nonworking Windows Store alias; no check is attributed to that failed command. The checks below were new inline Python programs executed via standard input, importing the reviewed `src/recovery.py`. They used separately written polynomial multiplication/reduction, trace, tensor evaluation, binary-rank, and direct balancing checks where relevant. They did not invoke or rely on the repository's existing test-suite conclusions.

1. **576 exhaustive fourth-vector cases.** For GF(4) with polynomial X^2+X+1 and GF(8) with polynomial X^3+X+1, fixed the three coordinate K-basis vectors and enumerated all q^3 fourth vectors. Direct tensor evaluations agreed with every computed fourth contraction; every returned balance-basis matrix satisfied the full direct balance equations. Whenever at least one fourth-vector coordinate generated the field, the balance dimension was s. The three-contraction dimensions were respectively 3 and 6, as predicted by s(s+1)/2.
2. **160 arbitrary binary-T defect cases.** Seed `2026102803`; 40 cases each at `(n,r)=(6,3),(8,3),(8,4),(10,4)`, with independent random support covectors, arbitrary exterior coefficients, and arbitrary binary endomorphisms T. All computed defect images matched independent pointwise constructions. In 93 cases the two-translate hypothesis held, and W(D_T E)=W(E) in every one. For 114 nonzero-error cases, the identity-map negative control gave D_I E=0, confirming that the translate hypothesis cannot simply be removed.
3. **1,020 exact rational probability checks.** Every `R=0,...,50` and `s=2R+5,...,2R+24`, computing tau from its divisor sum with exact integers and `Fraction`. Verified beta<1/2, gamma≥1/4, and `(1-beta) gamma≥1/8`. These finite checks supplement the symbolic derivation; they are not its proof.
4. **12 ordinary seeded clean recoveries within the theorem's sufficient regime.** Used s=5, R=0, h=1, polynomial X^5+X^2+1, coefficient 7, and `random.Random(seed)` for seeds 0 through 11. All returned verified nonzero certificates within their eight-trial budget. Trial counts were `[1,1,2,1,1,1,1,1,1,1,1,1]`; random-bit accounting matched `(4n+s) trials`. Independently evaluated 100 random physical triples per returned certificate, 1,200 total, using the newly written arithmetic and evaluation routines; every identity agreed.

The inline check programs and machine-readable receipts were not saved as reusable test artifacts. This saved report records their scope and observed results only. It must not be represented as an additional saved executable test suite or a reproducible receipt. The repository's existing scripts and receipts remain separate evidence and were not rerun by this reviewer.

## Limitations

- This is an AI review of the two named baseline files, not independent human peer review.
- No Lean source, axiom inventory, complete formalization, PDF layout, release archive, DOI, or bibliography claim was validated in this pass.
- No literature search was conducted; novelty and attribution are outside this review's evidence.
- Bounded checks do not establish asymptotic correctness or the success probability for all inputs. The publication recommendation rests primarily on the reconstructed prose argument.
- The ordinary seeded end-to-end tests in this pass use R=0. Arbitrary supported nonzero errors were exercised in the defect checks, not in a new ordinary-random full-recovery experiment at s≥2R+5.
- The source-level resource audit is not a machine-verified cost semantics or benchmark. A complete formal-certification claim remains unsupported by this review.

Remaining to-do list at the baseline review: update release-status wording; consider the two optional clarifications; complete the separately tracked Lean proof work before claiming complete formal certification. No unresolved publication-blocking mathematical finding from this review.

## Scoped review of the revised manuscript

Reviewed on 28 October 2026 after feedback incorporation. Revised `manuscript/main.tex` SHA-256: `A24C45D2D587060A780E6817C222D572E0FC292B81A4D4CEED69D5918F1B9B47`.

Scope: inspected the manuscript diff from the reviewed baseline, focusing on accepted A2/A3, the added field/coordinate/trace transport, preservation of the main theorem, and release/formal/review disclosures. This was a delta review; no full tests, Lean build, PDF build, or visual inspection were repeated. `git diff --check` reported no whitespace errors.

- **A1 resolved in the text:** the manuscript identifies itself as preprint v0.1.0 and replaces the Lean-before-release statement with an explicit partial-proof/future-certification disclosure. This text change is not itself evidence that publication or DOI archival has occurred.
- **A2 resolved:** the two-translate statement now directly requires injectivity of the restriction of T* to U, with the equivalent dimension condition. This is the same mathematical hypothesis as the original qualified formulation.
- **A3 resolved:** the resource paragraph distinguishes O(n^6) mutable-bit-array exterior construction from the conservative O(n^9) Python packed-integer construction, retaining the O(n^6) storage and headline soft-O(n^12) per-trial envelope.
- **Coordinate transport verified:** the added isomorphism sigma sends X to the sampled planted-field generator; `f(x)=B sigma(g(x))` with B invertible gives `c'=sigma^{-1}(c det B)≠0`. Applying determinant compatibility and trace invariance gives exactly the displayed compatible-tensor equality. The change supplies the previously implicit completeness bridge without strengthening assumptions.
- **Mode-image clarification verified:** the new text correctly states that displacement need not alternate in all three slots and that its W denotes only its third-mode image.
- **Main theorem preserved:** its hypotheses, success bound, trial/fair-bit caps, certificate meaning, soundness outside the promise, termination claim, and time/space conclusions are unchanged in the inspected diff.
- **Disclosures appropriate:** the abstract and formal section continue to disclaim full formal verification of both the main theorem and Python implementation. The assistance paragraph names the three actual model review passes and labels them AI-assisted internal reviews, expressly distinguishing human peer review and journal acceptance. The newly added Hora citation was not independently source-validated in this delta pass; source attribution review belongs to the saved Sol report.

Outcome: no new publication-blocking mathematical finding in the inspected changes. This recommendation still concerns an accurately labeled partially formalized preprint, not a fully Lean-certified theorem or verified Python program.

Remaining to-do list: complete package/release/DOI validation and the separately tracked Lean certification work; no unresolved mathematical correction from this review or its scoped delta pass.
