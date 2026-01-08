/**
 * String utility validators - startsWith, endsWith, contains, etc.
 * 
 * All validators are domain-based, enabling:
 * - Valid value generation
 * - Schema evolution via encapsulates()
 * - Set operations
 */

import {
  Regex,
  CompoundString as S,
  UnicodeString,
  chars,
  withGenerator,
  BaseValidator,
  ValidationResult,
  Domain as DomainType,
} from '@janus-validator/core';

// ============================================================================
// Helper functions
// ============================================================================

/**
 * Escape special regex characters in a string
 */
function escapeRegex(str: string): string {
  return str.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

/**
 * Generate a random string of printable ASCII characters
 */
function randomString(rng: { random: () => number }, minLen: number, maxLen: number): string {
  const length = Math.floor(rng.random() * (maxLen - minLen + 1)) + minLen;
  const chars = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789';
  let result = '';
  for (let i = 0; i < length; i++) {
    result += chars[Math.floor(rng.random() * chars.length)];
  }
  return result;
}

// ============================================================================
// StartsWith validator
// ============================================================================

/**
 * Validates strings that start with a specific prefix.
 * 
 * @param prefix - The prefix the string must start with
 * @param minLength - Minimum total string length (default: prefix length)
 * @param maxLength - Maximum total string length (default: prefix length + 100)
 * 
 * @example
 * ```typescript
 * const httpUrl = StartsWith('http://');
 * httpUrl.validate('http://example.com');  // valid
 * httpUrl.validate('https://example.com'); // invalid
 * 
 * // With length constraints
 * const shortPrefix = StartsWith('ID-', 5, 10);
 * shortPrefix.validate('ID-42');     // valid (length 5)
 * shortPrefix.validate('ID-123456'); // valid (length 9)
 * shortPrefix.validate('ID-');       // invalid (too short)
 * ```
 */
export const StartsWith = (
  prefix: string,
  minLength: number = prefix.length,
  maxLength: number = prefix.length + 100
) => {
  if (minLength < prefix.length) {
    throw new Error(`minLength (${minLength}) must be >= prefix length (${prefix.length})`);
  }
  
  const minSuffix = minLength - prefix.length;
  const maxSuffix = maxLength - prefix.length;
  
  // Build regex: ^prefix.{minSuffix,maxSuffix}$
  const pattern = new RegExp(
    `^${escapeRegex(prefix)}.{${minSuffix},${maxSuffix}}$`
  );
  
  // Use withGenerator to provide meaningful generation
  return withGenerator(
    Regex(pattern),
    (rng) => {
      const suffixLen = Math.floor(rng.random() * (maxSuffix - minSuffix + 1)) + minSuffix;
      return prefix + randomString(rng, suffixLen, suffixLen);
    }
  );
};

// ============================================================================
// EndsWith validator
// ============================================================================

/**
 * Validates strings that end with a specific suffix.
 * 
 * @param suffix - The suffix the string must end with
 * @param minLength - Minimum total string length (default: suffix length)
 * @param maxLength - Maximum total string length (default: suffix length + 100)
 * 
 * @example
 * ```typescript
 * const jsFile = EndsWith('.js');
 * jsFile.validate('app.js');      // valid
 * jsFile.validate('app.ts');      // invalid
 * 
 * // With length constraints
 * const email = EndsWith('@example.com', 15, 50);
 * email.validate('user@example.com');     // valid
 * email.validate('abc@example.com');      // invalid (too short, 15 chars min)
 * ```
 */
export const EndsWith = (
  suffix: string,
  minLength: number = suffix.length,
  maxLength: number = suffix.length + 100
) => {
  if (minLength < suffix.length) {
    throw new Error(`minLength (${minLength}) must be >= suffix length (${suffix.length})`);
  }
  
  const minPrefix = minLength - suffix.length;
  const maxPrefix = maxLength - suffix.length;
  
  // Build regex: ^.{minPrefix,maxPrefix}suffix$
  const pattern = new RegExp(
    `^.{${minPrefix},${maxPrefix}}${escapeRegex(suffix)}$`
  );
  
  // Use withGenerator to provide meaningful generation
  return withGenerator(
    Regex(pattern),
    (rng) => {
      const prefixLen = Math.floor(rng.random() * (maxPrefix - minPrefix + 1)) + minPrefix;
      return randomString(rng, prefixLen, prefixLen) + suffix;
    }
  );
};

// ============================================================================
// Contains validator
// ============================================================================

/**
 * Custom validator for strings that contain a specific substring.
 * Uses a simple approach without regex lookaheads (which aren't supported).
 */
class ContainsValidator extends BaseValidator<string> {
  public readonly domain: DomainType<string>;
  
  constructor(
    public readonly substring: string,
    public readonly minLength: number,
    public readonly maxLength: number
  ) {
    super();
    // Create a domain that generates strings containing the substring
    const baseValidator = UnicodeString(minLength, maxLength);
    this.domain = withGenerator(
      baseValidator,
      (rng) => {
        const remainingMin = Math.max(0, minLength - substring.length);
        const remainingMax = maxLength - substring.length;
        const totalRemaining = Math.floor(rng.random() * (remainingMax - remainingMin + 1)) + remainingMin;
        const prefixLen = Math.floor(rng.random() * (totalRemaining + 1));
        const suffixLen = totalRemaining - prefixLen;
        return randomString(rng, prefixLen, prefixLen) + substring + randomString(rng, suffixLen, suffixLen);
      }
    ).domain;
  }

  validate(input: unknown): ValidationResult<string> {
    if (typeof input !== 'string') {
      return this.error(`Expected string, got ${typeof input}`);
    }
    
    if (input.length < this.minLength) {
      return this.error(`Expected string length >= ${this.minLength}, got ${input.length}`);
    }
    
    if (input.length > this.maxLength) {
      return this.error(`Expected string length <= ${this.maxLength}, got ${input.length}`);
    }
    
    if (!input.includes(this.substring)) {
      return this.error(`Expected string to contain "${this.substring}"`);
    }
    
    return this.success(input);
  }
}

/**
 * Validates strings that contain a specific substring.
 * 
 * @param substring - The substring that must be present
 * @param minLength - Minimum total string length (default: substring length)
 * @param maxLength - Maximum total string length (default: substring length + 100)
 * 
 * @example
 * ```typescript
 * const hasError = Contains('error');
 * hasError.validate('An error occurred');  // valid
 * hasError.validate('All good');           // invalid
 * 
 * // With length constraints
 * const logEntry = Contains('INFO', 10, 200);
 * logEntry.validate('[INFO] Application started');  // valid
 * ```
 */
export const Contains = (
  substring: string,
  minLength: number = substring.length,
  maxLength: number = substring.length + 100
) => {
  if (minLength < substring.length) {
    throw new Error(`minLength (${minLength}) must be >= substring length (${substring.length})`);
  }
  
  return new ContainsValidator(substring, minLength, maxLength);
};

// ============================================================================
// Pattern-based startsWith/endsWith using CompoundString
// ============================================================================

/**
 * Creates a validator for strings starting with a literal prefix followed by a pattern.
 * Uses CompoundString for proper domain modeling and generation.
 * 
 * @param prefix - The literal prefix
 * @param suffixPattern - Validator for the suffix part (e.g., digits, alphanumeric)
 * 
 * @example
 * ```typescript
 * import { digits, alphanumeric } from '@janus-validator/core';
 * 
 * // ID format: "ID-" followed by 4-8 digits
 * const IdFormat = StartsWithPattern('ID-', digits(4, 8));
 * IdFormat.validate('ID-1234');      // valid
 * IdFormat.validate('ID-12345678');  // valid
 * IdFormat.validate('ID-abc');       // invalid
 * 
 * // Product code: "PROD_" followed by alphanumeric
 * const ProductCode = StartsWithPattern('PROD_', alphanumeric(5, 10));
 * ```
 */
export const StartsWithPattern = <T extends string>(
  prefix: string,
  suffixValidator: { domain: any; validate: (v: unknown) => any }
) => S(prefix, suffixValidator as any);

/**
 * Creates a validator for strings ending with a literal suffix preceded by a pattern.
 * Uses CompoundString for proper domain modeling and generation.
 * 
 * @param prefixPattern - Validator for the prefix part (e.g., digits, alphanumeric)
 * @param suffix - The literal suffix
 * 
 * @example
 * ```typescript
 * import { digits, letters } from '@janus-validator/core';
 * 
 * // File with .txt extension: any letters followed by ".txt"
 * const TxtFile = EndsWithPattern(letters(1, 20), '.txt');
 * TxtFile.validate('document.txt');  // valid
 * TxtFile.validate('notes.txt');     // valid
 * TxtFile.validate('file.doc');      // invalid
 * 
 * // Timestamp ending: digits followed by "Z"
 * const Timestamp = EndsWithPattern(digits(10, 13), 'Z');
 * ```
 */
export const EndsWithPattern = <T extends string>(
  prefixValidator: { domain: any; validate: (v: unknown) => any },
  suffix: string
) => S(prefixValidator as any, suffix);
