# @janus-validator/domain

Domain classes for the Janus Validator library. Domains represent the set of valid values for a validator and are used for:

- **Compatibility reasoning** - Check if one domain encapsulates (is a superset of) another
- **Generation** - Generate random values from a domain (via generator strategies in core)
- **Schema introspection** - Understand the structure and constraints of validators

## Installation

```bash
npm install @janus-validator/domain
```

## Usage

```typescript
import {
  Domain,
  DomainType,
  FiniteDomain,
  ContiguousDomain,
  ContiguousType,
  StringDomain,
} from '@janus-validator/domain';

// Create a finite domain with specific values
const colorDomain = new FiniteDomain(['red', 'green', 'blue']);

// Create a contiguous numeric domain
const ageDomain = new ContiguousDomain(ContiguousType.INTEGER, 0, 120);

// Check if one domain encapsulates another
const wideRange = new ContiguousDomain(ContiguousType.INTEGER, 0, 100);
const narrowRange = new ContiguousDomain(ContiguousType.INTEGER, 10, 50);

const result = wideRange.encapsulates(narrowRange);
// result.result === 'true' (wideRange contains all values in narrowRange)
```

## Domain Types

- **FiniteDomain** - A fixed set of values
- **ContiguousDomain** - A numeric range (integer or float)
- **StringDomain** - Unicode strings with optional length constraints
- **CharSetDomain** - Characters from a defined set
- **RegexDomain** - Strings matching a regular expression
- **AlternationDomain** - Union of multiple domains
- **SequenceDomain** - Ordered sequence of domains
- **QuantifierDomain** - Repeated domain with min/max counts
- **StructDomain** - Object with named domain fields
- **BytesDomain** - Binary data with length constraints
- **BigIntDomain** - Arbitrary precision integers
- **CustomGeneratorDomain** - Domain with custom generation logic

## License

MIT

