# Team Rules: Test-Driven Development

- Always write a failing (red) automated test before adding new production code.
- Make the test as small and specific as possible; prefer unit-level, property-based where useful.
- Add only the minimal production code to make the current failing test pass (green).
- Refactor only after green, keeping tests green at all times.
- Keep new functionality covered: no merging if new code lacks tests that would fail without it.
- Prefer fast, deterministic tests; isolate external effects behind test seams/mocks.
- When fixing bugs, first reproduce with a failing test, then fix and keep the test.
- Add a matching test file for each class, mirroring the namespace/directory structure.
- Maintain coverage: do not reduce test coverage; coverage tooling must pass.

# Team Rules: ADR-Driven Development

- Each new piece of functionality must be justified by an ADR created before coding begins.
- ADRs must capture context, decision, alternatives, and consequences; keep them concise and reviewable.
- Mark ADR status explicitly (Proposed/Accepted/Deprecated/Superseded); link to related code/test changes.
- Do not merge code for new functionality without a corresponding Accepted ADR.

# Team Rules: Class Structure

- Favor class-based development where it keeps concerns cohesive and testable.
- Prefer encapsulation over inheritance when it makes sense; compose before extending.
- Use `protected` over `private` to allow controlled extension without breaking encapsulation.
- Keep each class in its own file, arranged in a sensible namespace/directory structure.

