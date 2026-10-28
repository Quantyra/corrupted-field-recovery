# Agy / configured Gemini review, 28 October 2026

Post-publication review of v0.1.0 and the proposed Lean completion plan. The CLI was explicitly configured with `gemini-3.8-flash-high` (listed by Agy as Gemini 3.8 Flash (High)); its JSON response does not independently report a serving model identifier. The actual successful response follows. This is an AI review, not human peer review or formal certification.

Input: `artifacts/cross-provider-review-inputs.json`. Prior reviewer reports were excluded, but the supplied plan contained their summary, so the pass was not fully blind. The provider reports text/source inspection only, with no code or Lean execution. The CLI warned that plan mode was ineffective with slash-command expansion disabled; read-only scope was requested in the prompt, and no tracked source modification was observed. Its returned local file links are normalized to the published source and unreliable line fragments removed; numeric locations in the response may refer to packet offsets. Findings are reviewer assertions, evaluated separately in the disposition.

---

# Independent Mathematical and Formalization Review: Certified Recovery of Trace-Determinant Structure Under Low-Dimensional Corruption

**Review Baseline:** Preprint v0.1.0 (`DOI 10.5281/zenodo.23744566`, commit `1de9785ec38d6fa4064b0279e2a444e47a2f2413`)  
**Scope of Materials Inspected:** Complete review packet containing [manuscript/main.tex](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/manuscript/main.tex), [src/recovery.py](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/src/recovery.py), [tests/check_recovery.py](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/tests/check_recovery.py), [CorruptedFieldRecovery.lean](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/CorruptedFieldRecovery.lean), [CorruptedFieldRecovery/Defect.lean](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/CorruptedFieldRecovery/Defect.lean), [CorruptedFieldRecovery/Independent.lean](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/CorruptedFieldRecovery/Independent.lean), [checks/Audit.lean](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/checks/Audit.lean), [formal/coverage.json](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/formal/coverage.json), and the Proposed Lean Completion Plan.

---

## 1. Review Scope and Verdict

### Scope of Inspection
- **Mathematical Core:** The complete algebraic pipeline of Theorem 1, including the four-contraction identification ([Lemma 1](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/manuscript/main.tex)), the two-translate defect-image recovery ([Lemma 2](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/manuscript/main.tex)), the conditional sampling probability bounds ($\beta, \gamma$, and overall good-trial rate $2^{-4R-3}$ under $s \ge 2R + 5$), exact certificate soundness, and the bit-time/working-space resource envelopes.
- **Implementation & Companion Source:** Symbolic and index alignment between [manuscript/main.tex](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/manuscript/main.tex), the executable prototype in [src/recovery.py](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/src/recovery.py), and test fixtures in [tests/check_recovery.py](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/tests/check_recovery.py).
- **Formal Verification Status:** Lean 4 declarations in [CorruptedFieldRecovery/Defect.lean](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/CorruptedFieldRecovery/Defect.lean) and [CorruptedFieldRecovery/Independent.lean](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/CorruptedFieldRecovery/Independent.lean), the coverage status in [formal/coverage.json](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/formal/coverage.json), and the proposed 8-milestone completion roadmap (M0–M7).

### Verdict: **SOUND MATHEMATICAL CORE; PARTIAL LEAN COVERAGE; REALISTIC COMPLETION PLAN REQUIRING OPERATIONAL REFINEMENT**
- **Headline Mathematics:** The mathematical construction in Theorem 1 is **conceptually and algebraically sound**. No fatal counterexample, dimension collapse, or probabilistic flaw was found. The four contractions correctly eliminate off-diagonal blocks and isolate scalar multiplication; the two-translate difference operator provably cancels the uncorrupted component and recovers $W(E)$; the conditional fiber bounds on non-generators and bad translate positions hold under $s \ge 2R + 5$; and the certificate verifier guarantees soundness unconditionally.
- **Formal Status:** As accurately self-reported in [formal/coverage.json](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/formal/coverage.json), only the abstract algebraic kernel of mode-image recovery ([`CorruptedFieldRecovery.two_translate_of_disjoint`](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/CorruptedFieldRecovery/Independent.lean)) is currently proved in Lean 4. The concrete binary model, four contractions, finite sampling, deterministic constructor, certificate equivalence, and cost accounting remain unformalized.
- **Completion Plan:** The proposed milestone decomposition (M0–M7) correctly identifies all major formalization gaps, but requires structural adjustments regarding the operational cost semantics and probability space representation to avoid severe formalization bottlenecks in Lean 4.

---

## 2. Ranked Findings

### Finding 1: Operational Bit-Machine Model in M0/M6 Poses High Risk of Formalization Stall
- **Severity:** Moderate (Formalization Risk)
- **Location:** Proposed Lean Completion Plan, Section M0 (lines 1398–1402) & Section M6 (lines 1474–1485).
- **Reasoning:** M0 and M6 stipulate defining an operational cost model with "finite binary arrays/words, charged read/write/XOR/Boolean operations... live storage... and serialized output" to certify the bit-time $\widetilde O(2^{4R} h n^{12})$ and space $\widetilde O(n^8 + \log(h+1))$ bounds. Mathlib 4 lacks an established, ergonomic bit-level RAM or Turing-machine cost library. Attempting to define an imperative bit-addressable machine semantics with heap allocation, pointer manipulation, and candidate deallocation inside Lean 4 will introduce an enormous verification burden that dwarfs the algebraic proof.
- **Proof Gap / Recommendation:** Decouple algorithmic step complexity from physical bit simulation. Formalize the constructor as a functional program instrumented with an operational cost monad (`Writer (Sum Nat)` or step-counting recurrence) tracking primitive mathematical operations (field ops, vector XORs, matrix pivot steps, polynomial divisions). Separately prove explicit bit-size upper bounds for intermediate representations (words of size $s$, vectors of length $n$, $n \times n$ matrices) and compose them to derive the asymptotic bit envelopes.

---

### Finding 2: Global Invertibility Hypothesis Discrepancy in Formalized Two-Translate Lemma
- **Severity:** Low (Formalization Inconsistency)
- **Location:** [CorruptedFieldRecovery/Independent.lean](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/CorruptedFieldRecovery/Independent.lean) (`two_translate_of_disjoint`) vs. [manuscript/main.tex](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/manuscript/main.tex) (Lemma 2).
- **Reasoning:** In the manuscript, Lemma 2 assumes only that $U \cap T^* U = 0$ and that the restriction $T^*|_U$ is injective ($\dim T^* U = \dim U$). It does *not* assume $T$ is globally invertible on all of $V$. In contrast, `two_translate_of_disjoint` requires `T : V ≃ₗ[F] V` (a global linear equivalence).
- **Impact:** While the end-to-end recovery algorithm applies $T$ as scalar multiplication by $t \in K^\times$ (which is indeed globally invertible on $V$), the existing Lean theorem does not yet prove the full, more general claim of Lemma 2.
- **Proof Gap / Recommendation:** In M2, either:
  1. Generalize `two_translate_of_disjoint` to drop global invertibility, using the injectivity of $T^*|_U$ to construct a right inverse on the support image via quotient projection; or
  2. Formally discharge the global invertibility hypothesis by proving that scalar multiplication by any nonzero element of $\mathbb{F}_{2^s}$ on $K^3$ induces a global `LinearEquiv` on $V$.

---

### Finding 3: Unconditional Certificate Soundness Requires Explicit Non-Triviality Guard ($R < n$)
- **Severity:** Low (Theoretical Clarification)
- **Location:** [manuscript/main.tex](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/manuscript/main.tex), [L312-L319](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/manuscript/main.tex); [src/recovery.py](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/src/recovery.py) (`verify`).
- **Reasoning:** The manuscript states: *"Every accepted representation is sound even if the sufficient promise fails."* Section 5 justifies that the compatible coefficient $c$ cannot accidentally be zero because a nonzero trace-determinant form has mode image $V^*$ ($\dim = n$), whereas an error supported on $U$ has mode image $\le R < n$.
  However, the input validation allows $0 \le R \le n$. If $R = n$, the error support could span all of $V^*$, which would allow a trivial decomposition where the error absorbs the entire tensor and $c$ is unconstrained. Under the sufficient condition $s \ge 2R + 5$, we have $n = 3s \ge 6R + 15 > R$, guaranteeing $R < n$ strictly.
- **Proof Gap / Recommendation:** In the formal statement of certificate soundness in M1/M4, ensure that the guarantee *"the compatible component is non-trivial and uniquely separated from error"* explicitly carries the hypothesis $R < n$. This is always true under the promise, but must be explicitly accounted for when asserting soundness outside the promise.

---

### Finding 4: Discrete Probability Tape Formalization vs. Infinite Probability Spaces
- **Severity:** Low (Formalization Architecture)
- **Location:** Proposed Lean Completion Plan, Section M3 & M5 (lines 1463–1471).
- **Reasoning:** M5 contemplates coupling early-stopping execution to the full tape of $L = (4n+s)N$ bits. In Lean's Mathlib, general probability theory relies on measure theory (`MeasureSpace`, `Filtration`, stopping times). Setting up measure-theoretic stopping times on continuous or infinite bit-stream spaces for a simple bounded Bernoulli trial loop is needlessly complicated.
- **Proof Gap / Recommendation:** Specify the probability space in M5 strictly as the uniform discrete probability space over the finite type of tape blocks `Fin N → (Fin (4*n + s) → Bool)` with cardinality $2^{(4n+s)N}$. The probability of overall failure is bounded by the probability that *every* block index $k \in \{1, \dots, N\}$ fails the algebraic good-event criteria. Since the good-event condition for block $k$ depends solely on coordinate projections, block failure events are mutually independent cylinder sets, giving $\Pr(\bigcap_{k=1}^N \text{Fail}_k) = \prod_{k=1}^N \Pr(\text{Fail}_k) \le (1 - 2^{-4R-3})^N \le 2^{-h}$ via elementary discrete counting.

---

### Finding 5: Greedy Module Basis Construction Depends on Linear Independence in Quotients
- **Severity:** Informational (Verification Assurance)
- **Location:** [manuscript/main.tex](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/manuscript/main.tex), [L281-L287](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/manuscript/main.tex); [src/recovery.py](https://github.com/Quantyra/corrupted-field-recovery/blob/v0.1.0/src/recovery.py) (`certify_field`).
- **Reasoning:** In `certify_field`, the basis of $V$ over $K \cong \mathbb{F}_2[T]$ is selected greedily from the standard physical basis $\{e_0, \dots, e_{n-1}\}$. One must ensure that standard basis vectors always span the quotient module $V / W$ at each step.
- **Verification:** Since $\{e_0, \dots, e_{n-1}\}$ spans $V$ over $\mathbb{F}_2$, their residue classes generate $V/W$ over $\mathbb{F}_2$, and a fortiori over $K$. Since $K$ is a field and $W$ is a proper $K$-subspace, $V/W$ is a non-trivial vector space over $K$, so at least one $e_j$ must have a nonzero class. Thus, the greedy search over physical basis vectors is mathematically guaranteed to terminate in exactly 3 steps. The Lean proof in M2 will proceed smoothly via `Submodule.span`.

---

## 3. Recommended Changes to the Lean Completion Plan

| Milestone | Proposed Target in Plan | Recommended Modification / Refinement | Rationale |
|---|---|---|---|
| **M0 (S007)** | Operational bit-machine semantics with physical array allocation/charges. | **Replace full bit-machine semantics with a functional Step-Cost Monad.** Define operational cost signatures over structured binary matrices and finite field operations. | Prevents getting bogged down in low-level memory allocation, bit-packing, and pointer arithmetic proofs. |
| **M1 (S008)** | Binary tensor model and certificate predicate. | **Include explicit alternating vs. symmetric distinction in char 2.** Formalize that $E(x,x,z) = 0$ strictly implies symmetry $E(x,y,z) = E(y,x,z)$, but symmetry alone is insufficient over $\mathbb{F}_2$. | Avoids under-constraining the error model in characteristic 2. |
| **M2 (S009)** | Field identification, coordinate transport, and defect bridge. | **Split M2 into two sub-milestones:** <br>• M2a: Pure field theory and four-contraction balance theorem.<br>• M2b: Coordinate transport, $\det$ scaling, trace invariance, and defect specialization. | M2 is currently the largest mathematical hurdle in the plan; splitting it creates an independently reviewable algebraic checkpoint. |
| **M3 (S010)** | Finite sampling bounds and conditional probabilities. | **Use Fintype counting measures rather than general measure theory.** Formalize conditional bounds via fiber cardinalities of linear maps: $|\ker(\pi_1|_A)| \le q^2$. | Mathlib's discrete cardinality lemmas (`Finset.card`) are fully constructive and avoid measure-theoretic overhead. |
| **M4 (S011)** | Deterministic constructor and coefficient checker. | **Formalize Ben-Or polynomial irreducibility via Mathlib's finite field roots.** Connect `gcd(X^(2^k) - X, p) = 1` directly to minimal polynomials of elements in $\mathbb{F}_{2^s}$. | Bridges the gap between algorithmic polynomial gcd and algebraic irreducibility. |
| **M5 (S012)** | Full constructor and probability amplification. | **Structure amplification over static product tape $(\mathbb{F}_2^{4n+s})^N$.** Model early-stopping probability as a cylinder-event bound rather than adaptive martingales. | Eliminates the need for filtration and stopping-time formalization. |
| **M6 (S013)** | Charged bit-time and live working space. | **Formalize cost bounds via recurrence bounds on input dimensions.** Prove bounding functions $T(n, R, h) \le C \cdot 2^{4R} h n^{12}$ based on step counts multiplied by maximum bit widths. | Keeps cost proofs within standard constructive algebra. |

---

## 4. Limitations of this Review

1. **Static Analysis of Packet Materials:** This review was conducted strictly by inspecting the text, Python source, tests, and Lean files provided in the packet. No external compilers, Lean 4 kernel builds (`lake build`), or test suites (`python tests/check_recovery.py`) were executed during this review pass.
2. **Lean Pinned Toolchain Compatibility:** The review evaluated the Lean declarations and syntax against standard Mathlib 4 conventions for Lean 4.30.0 / Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`, but did not generate Lean proof terms.
3. **Excluded Scopes:**
   - As mandated, this review does **not** certify Python source refinement (e.g., verifying that `src/recovery.py` is a semantically faithful realization of the Lean specification).
   - This review does **not** transfer the cubic tensor recovery theorem ($s \ge 2R + 5$) to the broader quantum phase-recovery application ($s \ge 7R + 5$).
   - This review is an automated expert agentic review, not human peer review or formal machine certification.

---

## 5. Unresolved Blocking Issues

1. **Toolchain & Axiomatic Allowlist Governance (M0 Prerequisite):**
   - The repository currently relies on `propext`, `Classical.choice`, and `Quot.sound`.
   - The completion plan must strictly ensure that subsequent computational milestones (especially M4 polynomial irreducibility and matrix inversion) do not inadvertently introduce non-computable axioms (`Classical.indefiniteDescription`) into executable constructor evaluation paths, which would invalidate `#eval` and code generation.
2. **Separation of Certificate Soundness from Planted Witness Uniqueness:**
   - The manuscript and algorithm explicitly return *some* verified compatible representation; they do not prove uniqueness of the planted field $K$ or error support $U_*$.
   - The Lean theorem targets must maintain this existential quantifier structure: the final theorem must conclude $\exists (K', f', c', E'), \dots$, matching the verifier output rather than asserting recovery of the exact planted tuple $(K, f, c, E)$.

---

### Final Evaluation Summary
The mathematical proof of Theorem 1 in the preprint v0.1.0 is sound, elegant, and ready for full formalization. The proposed 8-milestone completion plan provides a solid foundation. Adopting the recommendations in Section 3—specifically using a step-cost monad instead of an imperative bit-machine, employing finite counting measures for sampling, and splitting M2 into two focused algebraic stages—will ensure the Lean formalization proceeds to complete certification without blocking bottlenecks.

