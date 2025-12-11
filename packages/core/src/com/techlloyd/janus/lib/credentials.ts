/**
 * Credential validators - passwords, usernames, PINs
 */

import { S, R, O, Or, alphanumeric, digits, letters, lower, upper, chars } from '../DSL';
import { createCaptureGroup } from '../combinators/Capture';
import { UnicodeString } from '../combinators/UnicodeString';

// ============================================================================
// Usernames
// ============================================================================

/**
 * Basic username: 3-20 alphanumeric characters and underscores, starts with letter
 */
export const Username = () => R(/^[a-zA-Z][a-zA-Z0-9_]{2,19}$/);

/**
 * Username with dots allowed (e.g., for emails): 3-30 chars
 */
export const UsernameWithDots = () => R(/^[a-zA-Z][a-zA-Z0-9_.]{2,29}$/);

/**
 * Handle/mention style: starts with @, 1-15 alphanumeric
 */
export const Handle = () => R(/^@[a-zA-Z][a-zA-Z0-9_]{0,14}$/);

// ============================================================================
// Passwords
// ============================================================================

/**
 * Basic password: 8-128 characters, any printable
 * Note: Uses UnicodeString for full character support
 */
export const Password = () => UnicodeString(8, 128);

/**
 * Strong password: 8-128 chars, requires uppercase, lowercase, digit, special char
 * Pattern: Upper + lower(2-6) + digits(2-4) + special(1-2) + trailing alphanumeric
 */
export const StrongPassword = () => S(
  upper(1),
  lower(2, 6),
  digits(2, 4),
  chars('!@#$%^&*', 1, 2),
  alphanumeric(0, 50)
);

/**
 * Medium password: 8-64 chars with at least letters and numbers
 */
export const MediumPassword = () => S(
  letters(2, 8),
  digits(2, 4),
  alphanumeric(4, 50)
);

/**
 * PIN: exactly 4 digits
 */
export const PIN4 = () => S(digits(4));

/**
 * PIN: exactly 6 digits
 */
export const PIN6 = () => S(digits(6));

/**
 * PIN: 4 or 6 digits
 */
export const PIN = () => Or(PIN4(), PIN6());

/**
 * Password with confirmation - returns validator and context
 */
export function PasswordWithConfirmation(minLength: number = 8, maxLength: number = 128) {
  const { capture, ref, context } = createCaptureGroup();
  
  const validator = O({
    password: capture('pwd', UnicodeString(minLength, maxLength)),
    confirmPassword: ref<string>('pwd'),
  });

  return { validator, context };
}

// ============================================================================
// Authentication tokens
// ============================================================================

/**
 * JWT token format (header.payload.signature)
 * Each part is base64url encoded
 */
export const JWT = () => R(/^[A-Za-z0-9_-]+\.[A-Za-z0-9_-]+\.[A-Za-z0-9_-]+$/);

/**
 * API key: 32-64 alphanumeric characters
 */
export const APIKey = () => S(alphanumeric(32, 64));

/**
 * Bearer token header
 */
export const BearerToken = () => R(/^Bearer\s+[A-Za-z0-9_-]+$/);
