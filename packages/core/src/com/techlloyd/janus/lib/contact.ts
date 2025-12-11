/**
 * Contact information validators - email, phone numbers
 */

import { S, R, O, Or, digits, letters } from '../DSL';
import { UnicodeString } from '../combinators/UnicodeString';
import { withGenerator } from '../combinators/WithGenerator';

// Corporate email domains for generation
const CORPORATE_DOMAINS = [
  'acme.com', 'company.com', 'enterprise.io', 'corp.net', 'business.org',
  'tech.co', 'solutions.com', 'services.net', 'global.com', 'industries.com',
];

// ============================================================================
// Email
// ============================================================================

/**
 * Basic email format
 */
export const Email = () => R(/^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$/);

/**
 * Strict email with common TLDs only
 */
export const StrictEmail = () => R(/^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.(com|org|net|edu|gov|io|co|uk|de|fr|jp|au|ca)$/);

/**
 * Corporate email (no free email providers)
 * Note: This is a simplified check - uses negative lookahead to exclude common free providers
 */
export const CorporateEmail = () => withGenerator(
  R(/^[a-zA-Z0-9._%+-]+@(?!gmail|yahoo|hotmail|outlook|aol)[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$/),
  (rng) => {
    const chars = 'abcdefghijklmnopqrstuvwxyz';
    const name = Array.from({ length: 5 + Math.floor(rng.random() * 5) }, () =>
      chars[Math.floor(rng.random() * chars.length)]
    ).join('');
    const domain = CORPORATE_DOMAINS[Math.floor(rng.random() * CORPORATE_DOMAINS.length)];
    return `${name}@${domain}`;
  }
);

// ============================================================================
// Phone Numbers
// ============================================================================

/**
 * US phone number: (XXX) XXX-XXXX format
 */
export const USPhoneFormatted = () => S('(', digits(3), ') ', digits(3), '-', digits(4));

/**
 * US phone number: various formats
 */
export const USPhone = () => R(/^(\(\d{3}\)\s?|\d{3}[-.]?)\d{3}[-.]?\d{4}$/);

/**
 * International phone with country code: +X XXX XXX XXXX
 */
export const InternationalPhone = () => R(/^\+\d{1,3}[\s.-]?\d{1,4}[\s.-]?\d{1,4}[\s.-]?\d{1,9}$/);

/**
 * E.164 format: +XXXXXXXXXXX (up to 15 digits)
 */
export const E164Phone = () => R(/^\+[1-9]\d{1,14}$/);

/**
 * UK phone number
 */
export const UKPhone = () => R(/^(\+44\s?|0)(\d{2,4}\s?\d{3,4}\s?\d{3,4}|\d{10})$/);

// ============================================================================
// Social Media
// ============================================================================

/**
 * Twitter/X handle: @username (1-15 alphanumeric + underscore)
 */
export const TwitterHandle = () => R(/^@?[a-zA-Z0-9_]{1,15}$/);

/**
 * Instagram handle
 */
export const InstagramHandle = () => R(/^@?[a-zA-Z0-9_.]{1,30}$/);

/**
 * LinkedIn profile URL
 */
export const LinkedInURL = () => R(/^https?:\/\/(www\.)?linkedin\.com\/in\/[a-zA-Z0-9_-]+\/?$/);

// ============================================================================
// Contact form schemas
// ============================================================================

/**
 * Basic contact form
 */
export const ContactForm = () => O({
  name: UnicodeString(1, 100),
  email: Email(),
  message: UnicodeString(10, 5000),
});

/**
 * Full contact information
 */
export const FullContact = () => O({
  firstName: S(letters(1, 50)),
  lastName: S(letters(1, 50)),
  email: Email(),
  phone: Or(USPhone(), InternationalPhone()),
});
