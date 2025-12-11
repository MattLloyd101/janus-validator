/**
 * String combinator - builds formatted strings from component parts
 * 
 * Allows constructing string patterns without regex, making them more readable
 * and easier to generate valid examples for.
 */

import { Validator, ValidationResult, Domain, DomainType, StringDomain, FiniteDomain } from '../index';
import { Constant } from './Constant';

// ============================================================================
// Types
// ============================================================================

/**
 * A part of a compound string - either a literal string or a validator
 */
export type StringPart = string | Validator<string>;

/**
 * Domain for compound strings
 */
export interface CompoundStringDomain extends Domain<string> {
  type: DomainType.STRING_DOMAIN;
  _parts: StringPart[];
}

// ============================================================================
// Helper character sets
// ============================================================================

const DIGITS = '0123456789';
const LOWERCASE = 'abcdefghijklmnopqrstuvwxyz';
const UPPERCASE = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ';
const LETTERS = LOWERCASE + UPPERCASE;
const ALPHANUMERIC = LETTERS + DIGITS;
const HEX_LOWER = '0123456789abcdef';
const HEX_UPPER = '0123456789ABCDEF';

// ============================================================================
// Character set validator factory
// ============================================================================

/**
 * Creates a validator for a string of characters from a given character set
 */
function charSetValidator(chars: string, length: number | [number, number]): Validator<string> {
  const minLen = typeof length === 'number' ? length : length[0];
  const maxLen = typeof length === 'number' ? length : length[1];
  const charArray = chars.split('');
  const charSetRegex = new RegExp(`^[${escapeRegex(chars)}]{${minLen},${maxLen}}$`);

  return {
    validate: (input: unknown): ValidationResult<string> => {
      if (typeof input !== 'string') {
        return { valid: false, error: `Expected string, got ${typeof input}` };
      }
      if (input.length < minLen || input.length > maxLen) {
        return { 
          valid: false, 
          error: `Expected ${minLen === maxLen ? minLen : `${minLen}-${maxLen}`} characters, got ${input.length}` 
        };
      }
      if (!charSetRegex.test(input)) {
        return { valid: false, error: `String contains invalid characters` };
      }
      return { valid: true, value: input };
    },
    domain: {
      type: DomainType.STRING_DOMAIN,
      minLength: minLen,
      maxLength: maxLen,
      // Store char set for generation
      _charSet: charArray,
    } as StringDomain & { _charSet: string[] },
  };
}

function escapeRegex(str: string): string {
  return str.replace(/[.*+?^${}()|[\]\\-]/g, '\\$&');
}

// ============================================================================
// Built-in Part Validators
// ============================================================================

/**
 * Exactly n digits (0-9)
 */
export function digits(length: number): Validator<string>;
/**
 * Between min and max digits (0-9)
 */
export function digits(min: number, max: number): Validator<string>;
export function digits(minOrExact: number, max?: number): Validator<string> {
  return charSetValidator(DIGITS, max !== undefined ? [minOrExact, max] : minOrExact);
}

/**
 * Exactly n lowercase letters (a-z)
 */
export function lower(length: number): Validator<string>;
/**
 * Between min and max lowercase letters (a-z)
 */
export function lower(min: number, max: number): Validator<string>;
export function lower(minOrExact: number, max?: number): Validator<string> {
  return charSetValidator(LOWERCASE, max !== undefined ? [minOrExact, max] : minOrExact);
}

/**
 * Exactly n uppercase letters (A-Z)
 */
export function upper(length: number): Validator<string>;
/**
 * Between min and max uppercase letters (A-Z)
 */
export function upper(min: number, max: number): Validator<string>;
export function upper(minOrExact: number, max?: number): Validator<string> {
  return charSetValidator(UPPERCASE, max !== undefined ? [minOrExact, max] : minOrExact);
}

/**
 * Exactly n letters (a-zA-Z)
 */
export function letters(length: number): Validator<string>;
/**
 * Between min and max letters (a-zA-Z)
 */
export function letters(min: number, max: number): Validator<string>;
export function letters(minOrExact: number, max?: number): Validator<string> {
  return charSetValidator(LETTERS, max !== undefined ? [minOrExact, max] : minOrExact);
}

/**
 * Exactly n alphanumeric characters (a-zA-Z0-9)
 */
export function alphanumeric(length: number): Validator<string>;
/**
 * Between min and max alphanumeric characters (a-zA-Z0-9)
 */
export function alphanumeric(min: number, max: number): Validator<string>;
export function alphanumeric(minOrExact: number, max?: number): Validator<string> {
  return charSetValidator(ALPHANUMERIC, max !== undefined ? [minOrExact, max] : minOrExact);
}

/**
 * Exactly n hexadecimal characters (0-9a-f)
 */
export function hex(length: number): Validator<string>;
/**
 * Between min and max hexadecimal characters (0-9a-f)
 */
export function hex(min: number, max: number): Validator<string>;
export function hex(minOrExact: number, max?: number): Validator<string> {
  return charSetValidator(HEX_LOWER, max !== undefined ? [minOrExact, max] : minOrExact);
}

/**
 * Exactly n uppercase hexadecimal characters (0-9A-F)
 */
export function hexUpper(length: number): Validator<string>;
/**
 * Between min and max uppercase hexadecimal characters (0-9A-F)
 */
export function hexUpper(min: number, max: number): Validator<string>;
export function hexUpper(minOrExact: number, max?: number): Validator<string> {
  return charSetValidator(HEX_UPPER, max !== undefined ? [minOrExact, max] : minOrExact);
}

/**
 * Characters from a custom character set
 */
export function chars(charSet: string, length: number): Validator<string>;
export function chars(charSet: string, min: number, max: number): Validator<string>;
export function chars(charSet: string, minOrExact: number, max?: number): Validator<string> {
  return charSetValidator(charSet, max !== undefined ? [minOrExact, max] : minOrExact);
}

// ============================================================================
// String combinator
// ============================================================================

/**
 * Creates a validator for strings built from component parts.
 * 
 * Parts can be:
 * - Literal strings (matched exactly)
 * - Validators (validated and concatenated)
 * 
 * @example
 * ```typescript
 * // Date format: YYYY-MM-DD
 * const ISODate = String(digits(4), '-', digits(2), '-', digits(2));
 * 
 * // UUID: xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx
 * const UUID = String(
 *   hex(8), '-', hex(4), '-', hex(4), '-', hex(4), '-', hex(12)
 * );
 * 
 * // Credit card: XXXX XXXX XXXX XXXX
 * const CreditCard = String(
 *   digits(4), ' ', digits(4), ' ', digits(4), ' ', digits(4)
 * );
 * 
 * // Phone: (XXX) XXX-XXXX
 * const Phone = String('(', digits(3), ') ', digits(3), '-', digits(4));
 * ```
 */
export function String(...parts: StringPart[]): Validator<string> {
  // Convert all parts to validators - literals become Constant validators
  const validators = parts.map(part => 
    typeof part === 'string' ? Constant(part) : part
  );
  
  // Pre-compute length info for each validator
  const partInfo = validators.map(validator => {
    const domain = validator.domain;
    
    // Constant/FiniteDomain - fixed length
    if (domain.type === DomainType.FINITE_DOMAIN) {
      const value = (domain as FiniteDomain<string>).values[0];
      const length = value.length;
      return { validator, minLength: length, maxLength: length };
    }
    
    // StringDomain - variable length
    const stringDomain = domain as StringDomain & { _charSet?: string[] };
    return { 
      validator,
      minLength: stringDomain.minLength ?? 1,
      maxLength: stringDomain.maxLength ?? 100,
    };
  });

  return {
    validate: (input: unknown): ValidationResult<string> => {
      if (typeof input !== 'string') {
        return { valid: false, error: `Expected string, got ${typeof input}` };
      }

      let position = 0;
      const extractedParts: string[] = [];

      for (let i = 0; i < partInfo.length; i++) {
        const info = partInfo[i];
        
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
            const remainingPartInfo = partInfo.slice(i + 1);
            
            if (canMatchPartInfo(remainingInput, remainingPartInfo)) {
              extractedParts.push(slice);
              position += len;
              matched = true;
              break;
            }
          }
        }
        
        if (!matched) {
          // Generate helpful error message
          const domain = info.validator.domain;
          const actual = input.slice(position, position + info.maxLength);
          let expected: string;
          
          if (domain.type === DomainType.FINITE_DOMAIN) {
            // Constant/literal - show exact expected value
            expected = `Expected '${(domain as FiniteDomain<string>).values[0]}'`;
          } else {
            // Variable-length validator
            expected = `Expected ${info.minLength}-${info.maxLength} matching characters`;
          }
          
          return { 
            valid: false, 
            error: `${expected} at position ${position}, got '${actual}'` 
          };
        }
      }

      // Check we consumed the entire input
      if (position !== input.length) {
        return { 
          valid: false, 
          error: `Unexpected characters after position ${position}` 
        };
      }

      return { valid: true, value: input };
    },
    domain: {
      type: DomainType.STRING_DOMAIN,
      minLength: partInfo.reduce((sum, p) => sum + p.minLength, 0),
      maxLength: partInfo.reduce((sum, p) => sum + p.maxLength, 0),
      _parts: parts,
    } as CompoundStringDomain,
  };
}

/**
 * Check if remaining input can potentially match remaining parts
 */
function canMatchPartInfo(input: string, partInfo: { minLength: number }[]): boolean {
  const minNeeded = partInfo.reduce((sum, p) => sum + p.minLength, 0);
  return input.length >= minNeeded;
}

/** Alias for String */
export const CompoundString = String;
