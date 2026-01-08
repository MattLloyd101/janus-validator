/**
 * CompoundString combinator - builds formatted strings from component parts
 * 
 * Allows constructing string patterns without regex, making them more readable
 * and easier to generate valid examples for.
 */

import { Validator, BaseValidator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { Domain, DomainType, FiniteDomain, RegexDomain } from '../Domain';
import { Constant, ConstantValidator } from './Constant';

// ============================================================================
// Types
// ============================================================================

/**
 * A part of a compound string - either a literal string or a string domain.
 * When constructing a CompoundStringValidator, users pass validators which are converted to domains.
 * For generation, only string literals and domains are stored.
 */
export type StringPart = string | Domain<string>;

/**
 * Domain for compound strings
 */
export type CompoundStringDomain = RegexDomain & { _parts: StringPart[] };

type CharRange = { min: number; max: number };

function toCodePoint(char: string): number {
  const codePoint = char.codePointAt(0);
  if (codePoint === undefined) {
    throw new Error('Expected non-empty string for character range');
  }
  return codePoint;
}

function charRange(start: string, end: string): CharRange {
  const min = toCodePoint(start);
  const max = toCodePoint(end);
  if (min > max) {
    throw new Error('charRange start must be <= end');
  }
  return { min, max };
}

function charsToRanges(charset: string): CharRange[] {
  const seen = new Set<number>();
  const ranges: CharRange[] = [];
  for (const char of charset) {
    const cp = toCodePoint(char);
    if (seen.has(cp)) continue;
    seen.add(cp);
    ranges.push({ min: cp, max: cp });
  }
  return ranges;
}

function escapeForCharClass(char: string): string {
  if (char === ']' || char === '\\' || char === '^' || char === '-') {
    return '\\' + char;
  }
  return char;
}

function rangesToCharClass(ranges: readonly CharRange[]): string {
  return ranges
    .map((r) => {
      const minChar = String.fromCodePoint(r.min);
      const maxChar = String.fromCodePoint(r.max);
      if (r.min === r.max) return escapeForCharClass(minChar);
      return `${escapeForCharClass(minChar)}-${escapeForCharClass(maxChar)}`;
    })
    .join('');
}

function stripAnchors(regex: RegExp): string {
  let source = regex.source;
  if (source.startsWith('^')) {
    source = source.slice(1);
  }
  if (source.endsWith('$')) {
    source = source.slice(0, -1);
  }
  return source;
}


// ============================================================================
// Character set validator class
// ============================================================================

function escapeRegex(str: string): string {
  return str.replace(/[.*+?^${}()|[\]\\-]/g, '\\$&');
}

/**
 * Validator for a string of characters from a given character set.
 * 
 * Internally uses range-based representation for efficient storage and comparison.
 */
class CharSetValidator extends BaseValidator<string, RegexDomain> {
  public readonly domain: RegexDomain;
  public readonly minLength: number;
  public readonly maxLength: number;
  public readonly regexSource: string;
  private readonly charSetRegex: RegExp;

  /**
   * Create from ranges or a string of allowed characters.
   * @param charset - Either an array of CharRange or a string of allowed characters
   */
  constructor(
    charset: string | readonly CharRange[],
    minLength: number,
    maxLength: number
  ) {
    super();
    this.minLength = minLength;
    this.maxLength = maxLength;

    const ranges = typeof charset === 'string' ? charsToRanges(charset) : charset;
    const charClass = rangesToCharClass(ranges);
    this.regexSource = `[${charClass}]{${minLength},${maxLength}}`;
    this.charSetRegex = new RegExp(`^${this.regexSource}$`);
    this.domain = new RegexDomain(this.charSetRegex);
  }

  validate(input: unknown): ValidationResult<string> {
    if (typeof input !== 'string') {
      return this.error(`Expected string, got ${typeof input}`);
    }
    if (input.length < this.minLength || input.length > this.maxLength) {
      return this.error(`Expected ${this.minLength === this.maxLength ? this.minLength : `${this.minLength}-${this.maxLength}`} characters, got ${input.length}`);
    }
    if (!this.charSetRegex.test(input)) {
      return this.error(`Expected characters matching ${this.regexSource}, got "${input}"`);
    }
    return this.success(input);
  }
}

/**
 * Creates a validator for a string of characters from a given character set (string or ranges)
 */
function charSetValidator(charset: string | readonly CharRange[], length: number | [number, number]): CharSetValidator {
  const minLen = typeof length === 'number' ? length : length[0];
  const maxLen = typeof length === 'number' ? length : length[1];
  return new CharSetValidator(charset, minLen, maxLen);
}

// ============================================================================
// Predefined Character Ranges (more efficient than string conversion)
// ============================================================================

/** Range for digits 0-9 (U+0030 to U+0039) */
const DIGIT_RANGES: readonly CharRange[] = [charRange('0', '9')];

/** Range for lowercase letters a-z (U+0061 to U+007A) */
const LOWERCASE_RANGES: readonly CharRange[] = [charRange('a', 'z')];

/** Range for uppercase letters A-Z (U+0041 to U+005A) */
const UPPERCASE_RANGES: readonly CharRange[] = [charRange('A', 'Z')];

/** Ranges for all letters A-Za-z */
const LETTER_RANGES: readonly CharRange[] = [charRange('A', 'Z'), charRange('a', 'z')];

/** Ranges for alphanumeric 0-9A-Za-z */
const ALPHANUMERIC_RANGES: readonly CharRange[] = [charRange('0', '9'), charRange('A', 'Z'), charRange('a', 'z')];

/** Ranges for hex lowercase 0-9a-f */
const HEX_LOWER_RANGES: readonly CharRange[] = [charRange('0', '9'), charRange('a', 'f')];

/** Ranges for hex uppercase 0-9A-F */
const HEX_UPPER_RANGES: readonly CharRange[] = [charRange('0', '9'), charRange('A', 'F')];

// ============================================================================
// Built-in Part Validators
// ============================================================================

/**
 * Exactly n digits (0-9)
 */
export function digits(length: number): CharSetValidator;
/**
 * Between min and max digits (0-9)
 */
export function digits(min: number, max: number): CharSetValidator;
export function digits(minOrExact: number, max?: number): CharSetValidator {
  return charSetValidator(DIGIT_RANGES, max !== undefined ? [minOrExact, max] : minOrExact);
}

/**
 * Exactly n lowercase letters (a-z)
 */
export function lower(length: number): CharSetValidator;
/**
 * Between min and max lowercase letters (a-z)
 */
export function lower(min: number, max: number): CharSetValidator;
export function lower(minOrExact: number, max?: number): CharSetValidator {
  return charSetValidator(LOWERCASE_RANGES, max !== undefined ? [minOrExact, max] : minOrExact);
}

/**
 * Exactly n uppercase letters (A-Z)
 */
export function upper(length: number): CharSetValidator;
/**
 * Between min and max uppercase letters (A-Z)
 */
export function upper(min: number, max: number): CharSetValidator;
export function upper(minOrExact: number, max?: number): CharSetValidator {
  return charSetValidator(UPPERCASE_RANGES, max !== undefined ? [minOrExact, max] : minOrExact);
}

/**
 * Exactly n letters (a-zA-Z)
 */
export function letters(length: number): CharSetValidator;
/**
 * Between min and max letters (a-zA-Z)
 */
export function letters(min: number, max: number): CharSetValidator;
export function letters(minOrExact: number, max?: number): CharSetValidator {
  return charSetValidator(LETTER_RANGES, max !== undefined ? [minOrExact, max] : minOrExact);
}

/**
 * Exactly n alphanumeric characters (a-zA-Z0-9)
 */
export function alphanumeric(length: number): CharSetValidator;
/**
 * Between min and max alphanumeric characters (a-zA-Z0-9)
 */
export function alphanumeric(min: number, max: number): CharSetValidator;
export function alphanumeric(minOrExact: number, max?: number): CharSetValidator {
  return charSetValidator(ALPHANUMERIC_RANGES, max !== undefined ? [minOrExact, max] : minOrExact);
}

/**
 * Exactly n hexadecimal characters (0-9a-f)
 */
export function hex(length: number): CharSetValidator;
/**
 * Between min and max hexadecimal characters (0-9a-f)
 */
export function hex(min: number, max: number): CharSetValidator;
export function hex(minOrExact: number, max?: number): CharSetValidator {
  return charSetValidator(HEX_LOWER_RANGES, max !== undefined ? [minOrExact, max] : minOrExact);
}

/**
 * Exactly n uppercase hexadecimal characters (0-9A-F)
 */
export function hexUpper(length: number): CharSetValidator;
/**
 * Between min and max uppercase hexadecimal characters (0-9A-F)
 */
export function hexUpper(min: number, max: number): CharSetValidator;
export function hexUpper(minOrExact: number, max?: number): CharSetValidator {
  return charSetValidator(HEX_UPPER_RANGES, max !== undefined ? [minOrExact, max] : minOrExact);
}

/**
 * Characters from a custom character set
 */
export function chars(charSet: string, length: number): CharSetValidator;
export function chars(charSet: string, min: number, max: number): CharSetValidator;
export function chars(charSet: string, minOrExact: number, max?: number): CharSetValidator {
  return charSetValidator(charSet, max !== undefined ? [minOrExact, max] : minOrExact);
}

// ============================================================================
// CompoundString combinator
// ============================================================================

interface PartInfo {
  validator: Validator<string, Domain<string>>;
  minLength: number;
  maxLength: number;
}

/**
 * Validator for strings built from component parts.
 * 
 * Parts can be:
 * - Literal strings (matched exactly)
 * - Validators (validated and concatenated)
 * 
 * @example
 * ```typescript
 * // Date format: YYYY-MM-DD
 * const ISODate = CompoundString(digits(4), '-', digits(2), '-', digits(2));
 * 
 * // UUID: xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx
 * const UUID = CompoundString(
 *   hex(8), '-', hex(4), '-', hex(4), '-', hex(4), '-', hex(12)
 * );
 * 
 * // Credit card: XXXX XXXX XXXX XXXX
 * const CreditCard = CompoundString(
 *   digits(4), ' ', digits(4), ' ', digits(4), ' ', digits(4)
 * );
 * 
 * // Phone: (XXX) XXX-XXXX
 * const Phone = CompoundString('(', digits(3), ') ', digits(3), '-', digits(4));
 * ```
 */
export class CompoundStringValidator extends BaseValidator<string, CompoundStringDomain> {
  public readonly domain: CompoundStringDomain;
  private readonly partInfo: PartInfo[];
  private readonly validators: Validator<string, Domain<string>>[];

  constructor(parts: (string | Validator<string, Domain<string>>)[]) {
    super();
    
    // Convert all parts to validators - literals become Constant validators
    this.validators = parts.map((part) =>
      typeof part === 'string' ? Constant(part) : part
    );

    // Pre-compute length info for each validator (fail fast on unsupported parts)
    this.partInfo = this.validators.map((validator, index) => {
      const part = parts[index];
      const domain = validator.domain as Domain<unknown>;

      if (typeof part === 'string') {
        const length = part.length;
        return { validator, minLength: length, maxLength: length };
      }

      if (validator instanceof ConstantValidator && typeof validator.value === 'string') {
        const valueLength = validator.value.length;
        return { validator, minLength: valueLength, maxLength: valueLength };
      }

      if (validator instanceof CharSetValidator) {
        return {
          validator,
          minLength: validator.minLength,
          maxLength: validator.maxLength,
        };
      }

      if (domain.kind === DomainType.FINITE) {
        const finite = domain as FiniteDomain<unknown>;
        const values = finite.all;
        if (values.length === 1 && typeof values[0] === 'string') {
          const length = (values[0] as string).length;
          return { validator, minLength: length, maxLength: length };
        }
      }

      throw new Error('CompoundString parts must be literals, constant strings, or character-set validators');
    });

    const regexSource = parts
      .map((part, idx) => this.partToRegex(part, this.validators[idx]))
      .join('');

    const regexDomain = new RegexDomain(new RegExp(`^${regexSource}$`));
    this.domain = Object.assign(regexDomain, {
      _parts: parts.map((p) => (typeof p === 'string' ? p : p.domain)),
    }) as CompoundStringDomain;
  }

  validate(input: unknown): ValidationResult<string> {
    if (typeof input !== 'string') {
      return this.error(`Expected string, got ${typeof input}`);
    }

    let position = 0;
    const extractedParts: string[] = [];

    for (let i = 0; i < this.partInfo.length; i++) {
      const info = this.partInfo[i];
      
      // Try to match validator part
      // Try from maxLength down to minLength
      let matched = false;
      
      for (let len = info.maxLength; len >= info.minLength; len--) {
        if (position + len > input.length) continue;
        
        const slice = input.slice(position, position + len);
        const result = info.validator.validate(slice);
        
        if (result.valid) {
          // Check if remaining parts can still match
          const remainingInput = input.slice(position + len);
          const remainingPartInfo = this.partInfo.slice(i + 1);
          
          if (this.canMatchPartInfo(remainingInput, remainingPartInfo)) {
            extractedParts.push(slice);
            position += len;
            matched = true;
            break;
          }
        }
      }
      
      if (!matched) {
        // Generate helpful error message
        const domain = info.validator.domain as Domain<string>;
        const actual = input.slice(position, position + info.maxLength);
        let expected: string;

        if (domain.kind === DomainType.FINITE) {
          const finite = domain as FiniteDomain<string>;
          expected = `Expected '${finite.all[0]}'`;
        } else {
          expected = `Expected ${info.minLength}-${info.maxLength} matching characters`;
        }

        return this.error(`${expected} at position ${position}, got '${actual}'`);
      }
    }

    // Check we consumed the entire input
    if (position !== input.length) {
      return this.error(`Expected end of string at position ${position}, got "${input.slice(position)}"`);
    }

    return this.success(input);
  }

  /**
   * Check if remaining input can potentially match remaining parts
   */
  private canMatchPartInfo(input: string, partInfo: { minLength: number }[]): boolean {
    const minNeeded = partInfo.reduce((sum, p) => sum + p.minLength, 0);
    return input.length >= minNeeded;
  }

  private partToRegex(part: string | Validator<string, Domain<string>>, validator: Validator<string, Domain<string>>): string {
    if (typeof part === 'string') {
      return escapeRegex(part);
    }

    if (validator instanceof ConstantValidator && typeof validator.value === 'string') {
      return escapeRegex(validator.value);
    }

    if (validator instanceof CharSetValidator) {
      return validator.regexSource;
    }

    const domain = validator.domain as Domain<unknown>;
    if (domain.kind === DomainType.FINITE) {
      const finite = domain as FiniteDomain<unknown>;
      const values = finite.all;
      if (values.every((v) => typeof v === 'string')) {
        const escaped = values.map((v) => escapeRegex(v as string));
        return escaped.length === 1 ? escaped[0] : `(?:${escaped.join('|')})`;
      }
    }

    if (domain instanceof RegexDomain) {
      return `(?:${stripAnchors(domain.pattern)})`;
    }

    throw new Error('Unsupported validator part for compound string');
  }
}

/**
 * Creates a validator for strings built from component parts.
 */
export function CompoundString(...parts: (string | Validator<string, Domain<string>>)[]): CompoundStringValidator {
  return new CompoundStringValidator(parts);
}

/** @deprecated Use CompoundString instead */
export const StringValidator = CompoundStringValidator;

