/**
 * Contact information validators - email, phone numbers
 */

import { Regex } from '../combinators/Regex';
import { CompoundString as S, digits, letters } from '../combinators/CompoundString';
import { Struct } from '../combinators/Struct';
import { Alternation } from '../combinators/Alternation';
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
export const Email = () => Regex(/^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$/);

/**
 * Strict email with common TLDs only
 */
export const StrictEmail = () => Regex(/^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.(com|org|net|edu|gov|io|co|uk|de|fr|jp|au|ca)$/);

/**
 * Corporate email (no free email providers)
 * Note: This validates basic email format. Use custom validation logic to exclude
 * specific domains like gmail, yahoo, etc. Generation produces corporate-style domains.
 */
export const CorporateEmail = () => withGenerator(
  Regex(/^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$/),
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
export const USPhone = () => Regex(/^(\([0-9]{3}\)[ ]?|[0-9]{3}[-.]?)[0-9]{3}[-.]?[0-9]{4}$/);

/**
 * International phone with country code: +X XXX XXX XXXX
 */
export const InternationalPhone = () => Regex(/^\+[0-9]{1,3}[ .-]?[0-9]{1,4}[ .-]?[0-9]{1,4}[ .-]?[0-9]{1,9}$/);

/**
 * E.164 format: +XXXXXXXXXXX (up to 15 digits)
 */
export const E164Phone = () => Regex(/^\+[1-9][0-9]{1,14}$/);

/**
 * UK phone number
 */
export const UKPhone = () => Regex(/^(\+44[ ]?|0)([0-9]{2,4}[ ]?[0-9]{3,4}[ ]?[0-9]{3,4}|[0-9]{10})$/);

// ============================================================================
// Social Media
// ============================================================================

/**
 * Twitter/X handle: @username (1-15 alphanumeric + underscore)
 */
export const TwitterHandle = () => Regex(/^@?[a-zA-Z0-9_]{1,15}$/);

/**
 * Instagram handle
 */
export const InstagramHandle = () => Regex(/^@?[a-zA-Z0-9_.]{1,30}$/);

/**
 * LinkedIn profile URL
 */
export const LinkedInURL = () => Regex(/^https?:\/\/(www\.)?linkedin\.com\/in\/[a-zA-Z0-9_-]+\/?$/);

// ============================================================================
// Contact form schemas
// ============================================================================

/**
 * Basic contact form
 */
export const ContactForm = () => Struct({
  name: UnicodeString(1, 100),
  email: Email(),
  message: UnicodeString(10, 5000),
});

/**
 * Full contact information
 */
export const FullContact = () => Struct({
  firstName: S(letters(1, 50)),
  lastName: S(letters(1, 50)),
  email: Email(),
  phone: Alternation.of(USPhone(), InternationalPhone()),
});
