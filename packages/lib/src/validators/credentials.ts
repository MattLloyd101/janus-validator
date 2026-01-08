/**
 * Credential validators - passwords, usernames, PINs
 * 
 * All validators are domain-based, enabling:
 * - Valid value generation
 * - Schema evolution via encapsulates()
 * - Set operations
 */

import {
  Regex,
  CompoundString as S,
  digits,
  alphanumeric,
  letters,
  lower,
  upper,
  chars,
  Alternation,
  UnicodeString,
} from '@janus-validator/core';

// ============================================================================
// Usernames
// ============================================================================

/**
 * Basic username: 3-20 alphanumeric characters and underscores, starts with letter
 */
export const Username = () => Regex(/^[a-zA-Z][a-zA-Z0-9_]{2,19}$/);

/**
 * Username with dots allowed (e.g., for emails): 3-30 chars
 */
export const UsernameWithDots = () => Regex(/^[a-zA-Z][a-zA-Z0-9_.]{2,29}$/);

/**
 * Handle/mention style: starts with @, 1-15 alphanumeric
 */
export const Handle = () => Regex(/^@[a-zA-Z][a-zA-Z0-9_]{0,14}$/);

// ============================================================================
// Passwords
// ============================================================================

/**
 * Basic password: 8-128 characters, any printable
 * Note: Uses UnicodeString for full character support
 */
export const Password = () => UnicodeString(8, 128);

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
export const PIN = () => Alternation.of(PIN4(), PIN6());

// ============================================================================
// Authentication tokens
// ============================================================================

/**
 * JWT token format (header.payload.signature)
 * Each part is base64url encoded
 */
export const JWT = () => Regex(/^[A-Za-z0-9_-]+\.[A-Za-z0-9_-]+\.[A-Za-z0-9_-]+$/);

/**
 * API key: 32-64 alphanumeric characters
 */
export const APIKey = () => S(alphanumeric(32, 64));

/**
 * Bearer token header
 */
export const BearerToken = () => Regex(/^Bearer[ ]+[A-Za-z0-9_-]+$/);
