# ADR-012: Extract Lib Package with Domain-Based Validators

## Status
Accepted

## Date
2026-01-08

## Context

The `@janus-validator/core` package currently includes a `lib/` subdirectory with pre-built validators for common patterns:
- Network validators (URL, IPv4, IPv6, Port, MAC address)
- Identifier validators (UUID, CUID, ULID, NanoID, Slug)
- Contact validators (Email, Phone)
- Location validators (Zip codes, Country codes)
- Financial validators (Credit card, Currency)
- Date/time validators (ISO timestamps, durations)

These validators serve a similar purpose to Zod's built-in refinements (`.email()`, `.url()`, `.uuid()`, etc.). However, there's a critical difference in approach:

**Refinement-based validators** (Zod's approach):
```typescript
z.string().email()  // Runtime check only, no domain knowledge
z.string().uuid()   // Generator produces random strings, not valid UUIDs
```

**Domain-based validators** (Janus's approach):
```typescript
Email()   // Proper domain that validates AND generates valid emails
UUIDv4()  // Proper domain that validates AND generates valid UUIDs
```

The domain-based approach aligns with Janus's core philosophy (ADR-002):
1. **Generation**: Domains can generate valid values (round-trip testing)
2. **Schema Evolution**: Domains participate in `encapsulates` checks
3. **Set Operations**: Domains support union/intersect/subtract

Currently, the lib validators are tightly coupled to core, making them difficult to:
- Version independently
- Tree-shake for smaller bundles
- Extend or customize for specific use cases
- Document as a standalone reference

## Decision

### 1) Create `@janus-validator/lib` as a Separate Package

Extract `packages/core/src/com/techlloyd/janus/lib/` into a new package: `packages/lib/`.

**Package structure:**
```
packages/lib/
├── src/
│   ├── index.ts
│   ├── domains/           # Domain implementations
│   │   ├── EmailDomain.ts
│   │   ├── UUIDDomain.ts
│   │   ├── URLDomain.ts
│   │   └── ...
│   ├── validators/        # Validator factory functions
│   │   ├── network.ts
│   │   ├── identifiers.ts
│   │   ├── contact.ts
│   │   └── ...
│   └── generators/        # Generator strategies for lib domains
│       ├── EmailGenerator.ts
│       └── ...
├── package.json
├── tsconfig.json
└── README.md
```

### 2) Domain-First Design (Not Refinement-Based)

Every lib validator MUST be backed by a proper domain that:
- Participates in `encapsulates()` checks
- Can generate valid values
- Supports set operations (where feasible)

**Anti-pattern (refinement-based):**
```typescript
// ❌ WRONG: Refinement doesn't inform the domain
const Email = () => UnicodeString(5, 254)
  .refine(s => /^[^@]+@[^@]+\.[^@]+$/.test(s), 'Invalid email');
// Generator produces: "x@#$%^" (random string, likely invalid)
// encapsulates() sees only: StringDomain(5, 254) - loses email semantics
```

**Correct pattern (domain-based):**
```typescript
// ✅ CORRECT: Domain knows it's an email
export const Email = () => Regex(/^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$/);
// Generator produces: "abc123@example.com" (valid email)
// encapsulates() sees: RegexDomain with email pattern - full semantics preserved

// For realistic generation, wrap with CustomGeneratorDomain
export const RealisticEmail = () => withGenerator(
  Email(),
  (rng) => generateRealisticEmail(rng)  // "alice.smith@gmail.com"
);
```

### 3) Schema Evolution via Domain Encapsulation

Because lib validators are proper domains, schema evolution checks work automatically:

```typescript
import { encapsulates } from '@janus-validator/domain';
import { Email, EmailV2 } from '@janus-validator/lib';

// Check if EmailV2 is backwards-compatible with Email
const result = encapsulates(EmailV2().domain, Email().domain);
if (result.result === 'true') {
  console.log('Safe migration: EmailV2 accepts all valid Email values');
}
```

This is only possible because lib validators expose their **semantic domain**, not just "string with a runtime check".

### 4) Categories of Lib Validators

Organize validators into semantic categories:

| Category | Validators | Domain Basis |
|----------|-----------|--------------|
| **Identifiers** | UUID, UUIDv4, CUID, ULID, NanoID, Slug, ObjectID, SnowflakeID | CompoundString, Regex |
| **Network** | URL, IPv4, IPv6, Port, Domain, MACAddress, CIDR | Regex, Integer |
| **Contact** | Email, Phone (US, E.164) | Regex, CompoundString |
| **Location** | ZipCode (US, UK), CountryCode, StateCode | CompoundString, Finite |
| **Financial** | CreditCard, Currency, Money, IBAN | CompoundString, Regex |
| **DateTime** | ISOTimestamp, ISODate, ISOTime, UnixTimestamp | CompoundString, Integer |
| **Text** | Emoji, Base64, Hex, JWT | Regex, CompoundString |
| **Codes** | HexColor, LanguageCode, LocaleCode, SemVer | CompoundString, Regex |

### 5) Realistic Data Presets (Generation Overrides)

For better test data, provide `Realistic*` variants using `CustomGeneratorDomain`:

```typescript
// Validates any email, generates any matching string
export const Email = () => Regex(/^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$/);

// Validates any email, generates realistic emails
export const RealisticEmail = () => withGenerator(
  Email(),
  (rng) => {
    const names = ['alice', 'bob', 'charlie', 'user', 'test'];
    const domains = ['gmail.com', 'example.com', 'company.org'];
    return `${pick(names, rng)}.${pick(names, rng)}@${pick(domains, rng)}`;
  }
);
```

**Important per ADR-002:** `CustomGeneratorDomain` is code-only and should be stripped during schema export. The semantic domain (`Email`) is preserved for compatibility checks.

### 6) Package Dependencies

```
@janus-validator/lib
  └── @janus-validator/core
        └── @janus-validator/domain
```

The lib package depends on core for:
- Validator base classes
- Combinator functions (Regex, CompoundString, etc.)
- Generator infrastructure

### 7) DSL Integration

The DSL package should re-export lib validators for convenience:

```typescript
// In @janus-validator/dsl
export { 
  Email, RealisticEmail,
  UUID, UUIDv4,
  URL, IPv4, IPv6, Port,
  // ...
} from '@janus-validator/lib';
```

Users can then use:
```typescript
import { O, U, Email, UUID } from '@janus-validator/dsl';

const User = O({
  id: UUID(),
  name: U(1, 100),
  email: Email(),
});
```

## Consequences

### Benefits

1. **True Schema Evolution**: Lib validators participate in `encapsulates()` because they expose semantic domains, not runtime-only checks.

2. **Correct Generation**: Generated values are always valid for the domain (e.g., `Email().generate()` produces valid emails).

3. **Independent Versioning**: Lib can be versioned separately from core, allowing faster iteration on common patterns.

4. **Tree-Shaking**: Users who don't need lib validators don't pay the bundle cost.

5. **Clear Separation**: Core remains focused on primitives and combinators; lib provides higher-level patterns.

6. **Extensibility Model**: Shows users how to create domain-based validators for their own patterns.

### Trade-offs

1. **Additional Package**: Users need to install another package for common validators.
   - Mitigated by DSL re-exports.

2. **Domain Complexity**: Some patterns (e.g., email with all RFC edge cases) may require complex regex domains.
   - Accept pragmatic subsets where full RFC compliance is impractical.

3. **Generator Overhead**: Realistic generators require curated data lists.
   - Keep data lists minimal; encourage users to provide their own via `withGenerator`.

### Migration Path

1. Keep `core/lib` as deprecated re-exports during transition
2. Add deprecation notices pointing to `@janus-validator/lib`
3. Remove `core/lib` in next major version

## Implementation Notes

### Domain-Based vs Refinement-Based Decision Tree

When adding a new lib validator, choose the approach based on:

| Question | Domain-Based | Refinement-Based |
|----------|--------------|------------------|
| Can it be expressed as regex/compound string? | ✅ Use domain | — |
| Does it need cross-field constraints? | — | ❌ Not supported (ADR-002) |
| Is the pattern decidable for encapsulation? | ✅ Use domain | — |
| Is it purely a runtime semantic check? | — | ⚠️ Use refine + document limitation |

**Rule**: Prefer domain-based. Only use refinements when domain representation is impossible (rare).

### Naming Convention

- `Email()`, `UUID()` — Semantic validators (validates and generates matching strings)
- `RealisticEmail()`, `RealisticUUID()` — Semantic + realistic generation
- `EmailPreset`, `UUIDPreset` — Deprecated names from core/lib, re-exported for compatibility

### Comparison with Zod

| Feature | Zod | janus-validator/lib |
|---------|-----|---------------------|
| `.email()` | Runtime refinement | `Email()` domain |
| `.uuid()` | Runtime refinement | `UUID()` domain |
| Generation | ❌ Not supported | ✅ Generates valid values |
| Schema evolution | ❌ No domain semantics | ✅ `encapsulates()` works |
| Customization | Override error message | Compose with `withGenerator` |

This is a key differentiator: Janus lib validators are **domains**, not just runtime checks.
