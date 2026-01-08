# @janus-validator/lib

Common validation patterns library for [Janus Validator](../core/README.md) - **domain-based validators** for emails, URLs, UUIDs, and more.

🚧 **Pre-1.0 notice:** This package has **not** reached `1.0` yet. Until then, the public API and behavior are **subject to change** between releases. If you need stability, **pin exact versions**.

## Why Domain-Based?

Unlike Zod's refinement-based validators (`.email()`, `.uuid()`), Janus lib validators are **domain-based**:

| Feature | Zod (Refinement) | Janus (Domain) |
|---------|------------------|----------------|
| Validation | ✅ Runtime check | ✅ Runtime check |
| Generation | ❌ Random strings | ✅ Valid values |
| Schema evolution | ❌ No semantics | ✅ `encapsulates()` works |
| Type narrowing | ✅ | ✅ |

This means:
- **Generation works**: `Email()` generates valid emails, not random strings
- **Schema evolution**: You can check if `EmailV2` is backwards-compatible with `Email`
- **Round-trip testing**: Generated values always validate

## Installation

```bash
npm install @janus-validator/lib @janus-validator/core
```

Or use via the DSL (recommended):

```bash
npm install @janus-validator/dsl @janus-validator/core
```

## Quick Start

```typescript
import { O, U } from '@janus-validator/dsl';
import { Email, UUIDv4, USPhone } from '@janus-validator/lib';
import { Generator } from '@janus-validator/core';

// Define a schema using lib validators
const User = O({
  id: UUIDv4(),
  name: U(1, 100),
  email: Email(),
  phone: USPhone(),
});

// Validate
const result = User.validate({
  id: '550e8400-e29b-41d4-a716-446655440000',
  name: 'Alice',
  email: 'alice@example.com',
  phone: '(555) 123-4567',
});

// Generate valid test data
const generator = new Generator({ random: Math.random });
const testUser = generator.generate(User.domain);
// { id: 'a1b2c3d4-e5f6-4789-a012-b3c4d5e6f789', name: '...', email: 'abc@def.com', ... }
```

## Validator Categories

### Identifiers

```typescript
import {
  UUID, UUIDv4, UUIDSimple, UUIDNoDashes,  // UUIDs
  CUID, ULID, NanoID, ShortID,              // Modern IDs
  ObjectID, SnowflakeID, IntegerID,         // Database IDs
  Slug, Base64ID,                           // URL-safe
  SemVer, SemVerFull,                       // Versioning
  MD5Hash, SHA1Hash, SHA256Hash, GitCommitHash,  // Hashes
  HexColor, HexColor6, HexColor3,           // Colors
  LanguageCode, LocaleCode,                 // i18n
} from '@janus-validator/lib';
```

### Network

```typescript
import {
  URL, SimpleURL, SecureURL,     // URLs
  WebSocketURL, FTPURL,
  Domain, Subdomain, Hostname,   // Domains
  IPv4, IPv6, IPAddress,         // IP addresses
  CIDR, PrivateIPv4,
  Port, WellKnownPort,           // Ports
  MACAddress,                    // Hardware
} from '@janus-validator/lib';
```

### Contact

```typescript
import {
  Email, StrictEmail, CorporateEmail,  // Emails
  USPhone, USPhoneFormatted,            // US phones
  InternationalPhone, E164Phone,        // International
  UKPhone,
  TwitterHandle, InstagramHandle,       // Social
  LinkedInURL,
} from '@janus-validator/lib';
```

### Credentials

```typescript
import {
  Username, UsernameWithDots, Handle,   // Usernames
  Password, StrongPassword, MediumPassword,  // Passwords
  PIN, PIN4, PIN6,                      // PINs
  JWT, APIKey, BearerToken,             // Tokens
} from '@janus-validator/lib';
```

### DateTime

```typescript
import {
  ISODate, ISODateTime,          // ISO formats
  USDate, EUDate,                // Regional
  Time24, Time24WithSeconds, Time12,  // Times
  Year, Month, DayOfMonth,       // Components
  Hour24, Hour12, Minute, Second,
  IANATimezone, UTCOffset,       // Timezones
  ISODuration, DurationMs,       // Durations
  CronExpression,                // Scheduling
} from '@janus-validator/lib';
```

### Location

```typescript
import {
  USZipCode, USZip5, USZipPlus4,  // US postal
  UKPostcode, CanadianPostalCode, GermanPLZ,  // International
  Latitude, Longitude, Coordinates, Coordinates3D,  // Geo
  CountryCodeAlpha2, CountryCodeAlpha3,  // Countries
  USStateCode,                    // States
} from '@janus-validator/lib';
```

### Financial

```typescript
import {
  CreditCardNumber, VisaCard, MasterCard, AmexCard,  // Cards
  CVV, CardExpiry,
  CurrencyCode, MoneyAmount, Price, Money,  // Money
  IBAN, SWIFT,                    // Banking
  USRoutingNumber, USBankAccountNumber,
  SSN, EIN, UKVAT, EUVAT,         // Tax IDs
} from '@janus-validator/lib';
```

### Realistic Presets

For better test data generation:

```typescript
import {
  // Names
  FirstName, LastName, FullName,
  
  // Usernames
  RealisticUsername,
  
  // Emails
  RealisticEmail, CorporateEmailPreset,
  
  // Addresses
  RealisticStreetAddress, RealisticCity,
  RealisticState, RealisticZipCode,
  
  // Phone
  RealisticUSPhone,
  
  // Business
  CompanyName, ProductName, LoremIpsum,
  
  // Dates
  RecentDate, FutureDate,
  
  // Money
  RealisticPrice,
} from '@janus-validator/lib';
```

## Schema Evolution

Because lib validators are domain-based, you can check compatibility:

```typescript
import { encapsulates } from '@janus-validator/domain';
import { Email } from '@janus-validator/lib';

// Define a new email validator that's more permissive
const EmailV2 = () => Regex(/^.+@.+$/);

// Check backwards compatibility
const result = encapsulates(EmailV2().domain, Email().domain);
if (result.result === 'true') {
  console.log('EmailV2 accepts all valid Email values - safe to migrate');
}
```

## Creating Custom Domain-Based Validators

Follow the domain-first pattern:

```typescript
import { Regex } from '@janus-validator/core';
import { withGenerator } from '@janus-validator/core';

// ✅ CORRECT: Domain-based validator
export const CustomEmail = () => Regex(/^[a-z]+@mycompany\.com$/);

// With realistic generation
export const RealisticCustomEmail = () => withGenerator(
  CustomEmail(),
  (rng) => {
    const names = ['alice', 'bob', 'charlie'];
    const name = names[Math.floor(rng.random() * names.length)];
    return `${name}@mycompany.com`;
  }
);

// ❌ WRONG: Refinement-based (loses domain semantics)
// const CustomEmail = () => UnicodeString(1, 100)
//   .refine(s => /^[a-z]+@mycompany\.com$/.test(s));
```

## License

MIT
