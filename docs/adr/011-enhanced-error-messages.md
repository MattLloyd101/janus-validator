# ADR-011: Enhanced Error Messages via Composition

## Status
Proposed

## Date
2026-01-08

## Context

Gap analysis against Zod revealed that janus-validator's error messages are limited:

1. **No path information** - Nested errors don't show where they occurred
2. **No custom messages** - Can't override default error messages
3. **No error codes** - Can't use for i18n or programmatic error handling
4. **No metadata** - Can't attach additional context

Zod provides rich error handling:

```typescript
// Zod errors include paths, codes, and custom messages
const schema = z.object({
  user: z.object({
    email: z.string().email('Invalid email format'),
  }),
});

const result = schema.safeParse({ user: { email: 'bad' } });
// {
//   success: false,
//   error: {
//     issues: [{
//       code: 'invalid_string',
//       message: 'Invalid email format',
//       path: ['user', 'email'],
//     }]
//   }
// }
```

Current janus-validator:
```typescript
const schema = O({
  user: O({
    email: R(/^[\w.]+@[\w.]+\.\w+$/),
  }),
});

const result = schema.validate({ user: { email: 'bad' } });
// { valid: false, error: 'Expected string matching /^...$/...' }
// No path, no customization
```

### Requirements

1. **Path tracking** - Errors include `path` array: `['user', 'email']`
2. **Custom messages** - `.message('Custom error text')`
3. **Error codes** - `.code('INVALID_EMAIL')` for i18n
4. **Descriptions** - `.describe('User email address')` for documentation
5. **Backward compatible** - Don't break existing code
6. **Composition-based** - Implement via wrapper validators

## Decision

### 1. Enhanced ValidationResult Type

Extend the `ValidationResult` type to include path and metadata:

```typescript
// packages/core/src/com/techlloyd/janus/ValidationResult.ts

/**
 * Result of a validation check.
 */
export type ValidationResult<T> =
  | { 
      valid: true; 
      value: T;
    }
  | {
      valid: false;
      /** Human-readable error message */
      error: string;
      /** 
       * Path to the error location as array of keys/indices.
       * Example: ['user', 'address', 0, 'zip'] for user.address[0].zip
       */
      path?: (string | number)[];
      /**
       * Path as dot-notation string for display.
       * Example: 'user.address.0.zip'
       */
      pathString?: string;
      /**
       * Error code for i18n or programmatic handling.
       * Example: 'INVALID_EMAIL', 'TOO_SHORT', 'REQUIRED'
       */
      code?: string;
      /**
       * Additional metadata attached by validators.
       */
      meta?: Record<string, unknown>;
      /**
       * Auto-generated valid example.
       */
      example?: T;
      /**
       * For composite types: per-field/element results.
       */
      results?: { [key: string]: ValidationResult<unknown> } | ValidationResult<unknown>[];
    };

/**
 * Helper to format path array as string.
 */
export function formatPath(path: (string | number)[]): string {
  return path
    .map((segment, i) => {
      if (typeof segment === 'number') {
        return `[${segment}]`;
      }
      return i === 0 ? segment : `.${segment}`;
    })
    .join('');
}

/**
 * Helper to prepend a segment to a path.
 */
export function prependPath(
  result: ValidationResult<unknown>,
  segment: string | number
): ValidationResult<unknown> {
  if (result.valid) return result;
  
  const newPath = [segment, ...(result.path ?? [])];
  return {
    ...result,
    path: newPath,
    pathString: formatPath(newPath),
  };
}
```

### 2. MessageValidator Wrapper

Override error messages:

```typescript
// packages/core/src/com/techlloyd/janus/combinators/Message.ts

import { Validator, BaseValidator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { Domain } from '../Domain';

/**
 * Wrapper validator that overrides error messages.
 */
export class MessageValidator<T, D extends Domain<T>> extends BaseValidator<T, D> {
  public readonly domain: D;

  constructor(
    private readonly inner: Validator<T, D>,
    private readonly messageOverride: string | ((error: string, value: unknown) => string)
  ) {
    super();
    this.domain = inner.domain;
  }

  validate(value: unknown): ValidationResult<T> {
    const result = this.inner.validate(value);
    
    if (result.valid) {
      return result;
    }

    const newMessage = typeof this.messageOverride === 'function'
      ? this.messageOverride(result.error, value)
      : this.messageOverride;

    return {
      ...result,
      error: newMessage,
    };
  }
}

/**
 * Override the error message of a validator.
 */
export function message<T, D extends Domain<T>>(
  validator: Validator<T, D>,
  msg: string | ((error: string, value: unknown) => string)
): Validator<T, D> {
  return new MessageValidator(validator, msg);
}
```

### 3. CodeValidator Wrapper

Add error codes:

```typescript
// packages/core/src/com/techlloyd/janus/combinators/Code.ts

/**
 * Wrapper validator that adds an error code.
 */
export class CodeValidator<T, D extends Domain<T>> extends BaseValidator<T, D> {
  public readonly domain: D;

  constructor(
    private readonly inner: Validator<T, D>,
    private readonly errorCode: string
  ) {
    super();
    this.domain = inner.domain;
  }

  validate(value: unknown): ValidationResult<T> {
    const result = this.inner.validate(value);
    
    if (result.valid) {
      return result;
    }

    return {
      ...result,
      code: this.errorCode,
    };
  }
}

/**
 * Add an error code to a validator for i18n or programmatic handling.
 */
export function code<T, D extends Domain<T>>(
  validator: Validator<T, D>,
  errorCode: string
): Validator<T, D> {
  return new CodeValidator(validator, errorCode);
}
```

### 4. DescribeValidator Wrapper

Add descriptions for documentation:

```typescript
// packages/core/src/com/techlloyd/janus/combinators/Describe.ts

/**
 * Wrapper validator that adds a description.
 * Description is stored in meta.description for documentation tools.
 */
export class DescribeValidator<T, D extends Domain<T>> extends BaseValidator<T, D> {
  public readonly domain: D;
  public readonly description: string;

  constructor(
    private readonly inner: Validator<T, D>,
    description: string
  ) {
    super();
    this.domain = inner.domain;
    this.description = description;
  }

  validate(value: unknown): ValidationResult<T> {
    const result = this.inner.validate(value);
    
    if (result.valid) {
      return result;
    }

    return {
      ...result,
      meta: {
        ...result.meta,
        description: this.description,
      },
    };
  }
}

/**
 * Add a description to a validator for documentation.
 */
export function describe<T, D extends Domain<T>>(
  validator: Validator<T, D>,
  description: string
): Validator<T, D> {
  return new DescribeValidator(validator, description);
}
```

### 5. Update Composite Validators for Path Tracking

Modify `StructValidator`, `SequenceValidator`, and `QuantifierValidator` to prepend paths:

```typescript
// In StructValidator.validate():
validate(input: unknown): ValidationResult<InferStructType<S>> {
  // ... existing validation logic ...

  for (const key of this.schemaKeys) {
    const fieldValidator = this.schema[key];
    const fieldResult = fieldValidator.validate(inputObj[key]);
    
    // Prepend field key to error path
    results[key] = prependPath(fieldResult, key);
    
    if (!fieldResult.valid) {
      hasErrors = true;
    }
  }

  // ... rest of method ...
}

// In SequenceValidator.validate():
validate(input: unknown): ValidationResult<TupleOfValidators<Vs>> {
  // ... existing validation logic ...

  for (let i = 0; i < this.validators.length; i++) {
    const elementResult = this.validators[i].validate(arr[i]);
    
    // Prepend index to error path
    results.push(prependPath(elementResult, i));
    
    if (!elementResult.valid) {
      hasErrors = true;
    }
  }

  // ... rest of method ...
}

// In QuantifierValidator.validate():
validate(input: unknown): ValidationResult<T[]> {
  // ... existing validation logic ...

  for (let i = 0; i < arr.length; i++) {
    const elementResult = this.validator.validate(arr[i]);
    
    // Prepend index to error path
    results.push(prependPath(elementResult, i));
    
    if (!elementResult.valid) {
      hasErrors = true;
    }
  }

  // ... rest of method ...
}
```

### 6. Fluent API Extension

```typescript
declare module '../../Validator' {
  interface BaseValidator<T, D extends Domain<T>> {
    /**
     * Override the error message.
     * @param msg Static message or function (originalError, value) => message
     * 
     * @example
     * I(0, 100).message('Age must be between 0 and 100')
     * U().message((err, val) => `Invalid input "${val}": ${err}`)
     */
    message(msg: string | ((error: string, value: unknown) => string)): Validator<T, D>;

    /**
     * Add an error code for i18n or programmatic handling.
     * 
     * @example
     * U().email().code('INVALID_EMAIL')
     */
    code(errorCode: string): Validator<T, D>;

    /**
     * Add a description for documentation.
     * 
     * @example
     * U(5, 100).email().describe('User email address')
     */
    describe(description: string): Validator<T, D>;
  }
}

BaseValidator.prototype.message = function<T, D extends Domain<T>>(
  this: Validator<T, D>,
  msg: string | ((error: string, value: unknown) => string)
): Validator<T, D> {
  return new MessageValidator(this, msg);
};

BaseValidator.prototype.code = function<T, D extends Domain<T>>(
  this: Validator<T, D>,
  errorCode: string
): Validator<T, D> {
  return new CodeValidator(this, errorCode);
};

BaseValidator.prototype.describe = function<T, D extends Domain<T>>(
  this: Validator<T, D>,
  description: string
): Validator<T, D> {
  return new DescribeValidator(this, description);
};
```

### 7. Error Formatting Utilities

```typescript
// packages/core/src/com/techlloyd/janus/errors/format.ts

import { ValidationResult } from '../ValidationResult';

export interface FormattedError {
  path: string;
  message: string;
  code?: string;
}

/**
 * Flatten a validation result into a list of errors.
 */
export function flattenErrors<T>(result: ValidationResult<T>): FormattedError[] {
  if (result.valid) return [];

  const errors: FormattedError[] = [];

  // If this result has nested results, recurse
  if (result.results) {
    if (Array.isArray(result.results)) {
      for (const childResult of result.results) {
        errors.push(...flattenErrors(childResult));
      }
    } else {
      for (const childResult of Object.values(result.results)) {
        errors.push(...flattenErrors(childResult));
      }
    }
  }

  // If no nested errors or this is a leaf error
  if (errors.length === 0 || !result.results) {
    errors.push({
      path: result.pathString ?? '',
      message: result.error,
      code: result.code,
    });
  }

  return errors;
}

/**
 * Format errors as a human-readable string.
 */
export function formatErrors<T>(result: ValidationResult<T>): string {
  const errors = flattenErrors(result);
  return errors
    .map(e => e.path ? `${e.path}: ${e.message}` : e.message)
    .join('\n');
}

/**
 * Format errors as JSON for API responses.
 */
export function errorsToJson<T>(result: ValidationResult<T>): object {
  const errors = flattenErrors(result);
  return {
    valid: false,
    errors: errors.map(e => ({
      path: e.path || null,
      message: e.message,
      code: e.code || null,
    })),
  };
}
```

## Usage Examples

```typescript
import { U, I, B, O, R } from '@janus-validator/dsl';
import { flattenErrors, formatErrors, errorsToJson } from '@janus-validator/core';

// Custom messages
const age = I(0, 150).message('Please enter a valid age between 0 and 150');

// Error codes for i18n
const email = R(/^[\w.]+@[\w.]+\.\w+$/)
  .message('Invalid email format')
  .code('INVALID_EMAIL');

// Descriptions for documentation
const username = U(3, 20)
  .describe('Unique username for login');

// Combined
const password = U(8, 100)
  .refine(s => /[A-Z]/.test(s), 'Must contain uppercase')
  .refine(s => /[0-9]/.test(s), 'Must contain digit')
  .message('Password does not meet requirements')
  .code('WEAK_PASSWORD')
  .describe('User account password');

// Nested schema with paths
const User = O({
  profile: O({
    name: U(1, 100).message('Name is required'),
    email: email,
  }),
  settings: O({
    notifications: B().default(true),
  }),
});

const result = User.validate({
  profile: {
    name: '',
    email: 'invalid',
  },
});

// Result includes paths:
// {
//   valid: false,
//   error: 'profile.name: Name is required; profile.email: Invalid email format',
//   results: {
//     profile: {
//       valid: false,
//       results: {
//         name: { valid: false, error: 'Name is required', path: ['profile', 'name'] },
//         email: { valid: false, error: 'Invalid email format', path: ['profile', 'email'], code: 'INVALID_EMAIL' },
//       }
//     }
//   }
// }

// Flatten for form handling
const errors = flattenErrors(result);
// [
//   { path: 'profile.name', message: 'Name is required' },
//   { path: 'profile.email', message: 'Invalid email format', code: 'INVALID_EMAIL' }
// ]

// Format for display
console.log(formatErrors(result));
// profile.name: Name is required
// profile.email: Invalid email format

// JSON for API response
const json = errorsToJson(result);
// {
//   valid: false,
//   errors: [
//     { path: 'profile.name', message: 'Name is required', code: null },
//     { path: 'profile.email', message: 'Invalid email format', code: 'INVALID_EMAIL' }
//   ]
// }

// Array paths
const List = O({
  items: oneOrMore(O({
    id: I(1),
    name: U(1, 50),
  })),
});

List.validate({
  items: [
    { id: 1, name: 'Valid' },
    { id: -1, name: '' },  // Invalid
  ],
});
// Errors at: items[1].id, items[1].name

// Dynamic messages
const quantity = I(1, 100).message((err, val) => 
  `Quantity ${val} is invalid. ${err}`
);
```

## Consequences

### Positive

1. **Rich errors** - Paths show exactly where problems are
2. **i18n ready** - Error codes enable translation
3. **API friendly** - JSON formatting for responses
4. **Form friendly** - Flat errors map to form fields
5. **Self-documenting** - Descriptions for schema docs
6. **Backward compatible** - Old code still works; path/code are optional

### Negative

1. **Memory overhead** - Each error carries more data
2. **Path computation** - Slight performance cost for path tracking
3. **Breaking change** - Composite validators need updates for path prepending

### Migration

Existing code continues to work. The new fields (`path`, `code`, `meta`) are optional. Users can gradually adopt custom messages and error codes.

## File Structure

```
packages/core/src/com/techlloyd/janus/
├── ValidationResult.ts         # Enhanced type + helpers
├── combinators/
│   ├── Message.ts              # MessageValidator
│   ├── Code.ts                 # CodeValidator
│   ├── Describe.ts             # DescribeValidator
│   └── Struct.ts               # Update for path tracking
├── errors/
│   ├── index.ts                # Re-exports
│   └── format.ts               # flattenErrors, formatErrors, errorsToJson
└── index.ts                    # Export new utilities
```

## Follow-ups

1. Add `.catch(fallback)` modifier - return fallback on validation failure
2. Consider internationalization helpers for error messages
3. Add schema introspection utilities (extract all descriptions, codes)
4. Consider structured error objects (like Zod's ZodError class)
5. Add error aggregation options (first error only vs all errors)
