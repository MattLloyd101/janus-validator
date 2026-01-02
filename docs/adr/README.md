# Architectural Decision Records

This directory contains Architectural Decision Records (ADRs) for the Janus Validator project.

## Index

| ADR | Title | Status |
|-----|-------|--------|
| [ADR-001](./001-avro-map-type-handling.md) | Avro Map Type Handling | Accepted |
| [ADR-002](./002-domain-relations-and-set-operations.md) | Domain Relations and Set Operations for Schema Compatibility | Accepted |
| [ADR-003](./003-property-based-testing-for-domain.md) | Property-Based Testing for the Domain Package | Accepted |
| [ADR-004](./004-regex-parser-and-domain-integration.md) | Regex Parser Extraction and RegexDomain AST Mapping | Accepted |
| [ADR-005](./005-domain-normalization-invariant.md) | Domain Normalization Invariant at Creation Time | Accepted |
| [ADR-006](./006-generators-to-domain.md) | Move Generators from Core to Domain Package | Proposed |
| (removed) | Certificate-Based Domain System / Serialization / Verification | Removed (pivoted to property-based testing) |

## What is an ADR?

An Architectural Decision Record captures an important architectural decision made along with its context and consequences. ADRs help:

- Document why decisions were made
- Onboard new team members
- Revisit decisions when context changes
- Avoid re-litigating settled discussions

## ADR Template

```markdown
# ADR-NNN: Title

## Status
[Proposed | Accepted | Deprecated | Superseded by ADR-XXX]

## Date
YYYY-MM-DD

## Context
What is the issue that we're seeing that is motivating this decision?

## Decision
What is the change that we're proposing and/or doing?

## Consequences
What becomes easier or more difficult because of this change?
```

