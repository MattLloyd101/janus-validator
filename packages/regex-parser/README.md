# @janus-validator/regex-parser

Portable regex AST parser shared across Janus packages. Enforces the portable subset (no flags/backrefs/lookarounds/\\w/\\s/\\b) and produces an AST for further analysis/mapping.

## Usage
```ts
import { parseRegexToAST } from '@janus-validator/regex-parser';

const ast = parseRegexToAST("^[A-Za-z0-9_]+$");
```

## Scripts
- `npm -w @janus-validator/regex-parser run build` — TypeScript compile to `dist/`.
- `npm -w @janus-validator/regex-parser test` — Jest tests.
- `npm -w @janus-validator/regex-parser run test:coverage` — Jest with coverage (strict thresholds).
- `npm -w @janus-validator/regex-parser run watch` — Build in watch mode.
- `npm -w @janus-validator/regex-parser run clean` — Remove `dist/`.

## Portable subset (enforced)
- Supported: literals/escapes for common controls, char classes/ranges (and negation), `.`, `^`, `$`, groups (capturing and `?:`), alternation, quantifiers `* + ? {n} {n,} {n,m}`.
- Rejected: flags, backreferences, lookarounds, inline-flag groups, non-portable escapes (`\\d`, `\\w`, `\\s`, `\\b`, etc.).

