# ADR-003: Certificate-Based Domain System with Trusted Kernel and ContiguousDomain

## Status
Accepted

## Date
2025-12-28

## Context
- Existing ADRs (ADR-001 Avro map handling, ADR-002 domain relations & set ops) emphasize exactness and defensiveness.
- We need a checkable, canonical representation for domains so operations are provably correct and normalization-friendly.
- The approach is to make certificates (ASTs) authoritative, with a small trusted kernel: `check`, `normalize`, and `eval`.

## Decision
Adopt a certificate-driven domain architecture with a trusted kernel and implement a discrete `ContiguousDomain` as the first concrete domain family.

Key elements
- Certificates are authoritative: every domain holds a `DomainCert<T>` AST; all operations construct new certificates, run `check`, optionally `normalize`, then return a domain from the resulting cert.
- Trusted kernel only: `checkCert`, `normalizeCert`, and `eval/contains` constitute the trusted code; domain wrappers are thin.
- Discrete ordered carriers: `ContiguousDomain` operates over `DiscreteOrdered<T>` witnesses (total order, `succ`/`pred`, optional `distance`/`show`).
- Empty/Universe: Empty as `FiniteCert([])`; universe carried by the domain wrapper (e.g., contiguous min/max with witness).

Certificate shapes (minimum viable set)
- `finite`, `contiguous`, `union`, `intersect`, `complement` (with `DiscreteOrdered` witness on contiguous certs).

Checker obligations (examples)
- Contiguous must have witness and `min <= max`.
- Children must check; complements rely on wrapper-provided universe.

Normalization rules (examples)
- Identity/annihilator: union with empty -> other; intersect with empty -> empty.
- Idempotence: union(x, x) = x; intersect(x, x) = x.
- Flatten unions/intersects; merge/clip contiguous ranges when overlapping/adjacent (same witness).

Evaluation
- `contains(cert, value, universe?)` defines membership; complement uses provided universe.
- Derived helpers: `isEmpty`, `maybeIsFinite`, `toString` for debug.

AbstractDomain contract
- Stores `cert` and `universe`; enforces check + normalize on construction.
- Operations (`union`, `intersect`, `complement`, `isDefinedAt`, `equals`) are cert-based.
- `encapsulates` uses a conservative `encapsulatesCert` decision procedure for supported fragments (contiguous/finite and reducible unions/intersects); never returns true unless proven.
- `fromCert` factory lets concrete families inject witnesses and wrap resulting certs.

ContiguousDomain
- Universe factory `universe(min, max, witness)`; range factory `range(universe, min, max)`; `empty()` yields `Finite([])`.
- Witness identity must match for merge/comparison.
- Range constructor rejects `min > max` (empty is explicit via `Finite([])`).

Testing requirements
- Kernel: checker rejects missing witness and invalid bounds; normalization merges ranges and simplifies empty; complement/union/intersect basics.
- ContiguousDomain: membership on bounds; union merge of adjacent/overlapping ranges; intersection clipping; encapsulation positive/negative cases; equals after normalization.
- Provide integer witness (`compare`, `succ`, `pred`, `distance`) for tests; property tests optional if fast-check available.

Non-goals
- Coq/OCaml extraction, continuous/float domains, complex composites (records/arrays/regex), SMT solving.

## Consequences
Benefits
- Sound-by-construction domains via checkable certificates and small trusted kernel.
- Normalization yields stable shapes for equality and encapsulation checks.
- Extensible: other domain families can reuse the kernel and cert AST.

Trade-offs / risks
- Additional boilerplate to route all operations through certificates.
- Conservative `encapsulates` may return false/unknown for unsupported fragments.

## Follow-ups / implementation plan
1) Add certificate types and checker.
2) Add normalization (including contiguous merge/clip).
3) Add evaluator (`contains`, emptiness, finiteness heuristics).
4) Implement `AbstractDomain` and `encapsulatesCert` (conservative rules only).
5) Implement `ContiguousDomain` + integer witness and factories.
6) Add kernel and domain tests (unit/property as available).

