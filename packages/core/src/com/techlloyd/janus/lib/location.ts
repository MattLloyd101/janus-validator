/**
 * Location validators - addresses, postal codes, coordinates
 */

import { Regex } from '../combinators/Regex';
import { CompoundString as S, digits, upper, alphanumeric, letters, chars } from '../combinators/CompoundString';
import { Float } from '../combinators/Float';
import { Struct } from '../combinators/Struct';
import { Alternation } from '../combinators/Alternation';
import { UnicodeString } from '../combinators/UnicodeString';

// ============================================================================
// Postal/ZIP Codes
// ============================================================================

/**
 * US ZIP code: 5 digits
 */
export const USZip5 = () => S(digits(5));

/**
 * US ZIP+4 code: 5 digits + dash + 4 digits
 */
export const USZipPlus4 = () => S(digits(5), '-', digits(4));

/**
 * US ZIP code (5 digits or 5+4)
 */
export const USZipCode = () => Alternation.of(USZip5(), USZipPlus4());

/**
 * UK postcode (case-insensitive - accepts both upper and lower case)
 * Format: A9 9AA, A99 9AA, AA9 9AA, AA99 9AA, A9A 9AA, AA9A 9AA
 */
export const UKPostcode = () => Regex(/^[A-Za-z]{1,2}[0-9][A-Za-z0-9]?[ ]*[0-9][A-Za-z]{2}$/);

/**
 * Canadian postal code: A1A 1A1 (case-insensitive)
 */
export const CanadianPostalCode = () => Regex(/^[A-Za-z][0-9][A-Za-z][ ]?[0-9][A-Za-z][0-9]$/);

/**
 * German postal code (PLZ): 5 digits
 */
export const GermanPLZ = () => S(digits(5));

/**
 * Generic postal code (alphanumeric, 3-10 chars)
 */
export const PostalCode = () => S(alphanumeric(3, 10));

// ============================================================================
// Geographic coordinates
// ============================================================================

/**
 * Latitude (-90 to 90)
 */
export const Latitude = () => Float(-90, 90);

/**
 * Longitude (-180 to 180)
 */
export const Longitude = () => Float(-180, 180);

/**
 * Geographic coordinates
 */
export const Coordinates = () => Struct({
  latitude: Latitude(),
  longitude: Longitude(),
});

/**
 * Coordinates with altitude
 */
export const Coordinates3D = () => Struct({
  latitude: Latitude(),
  longitude: Longitude(),
  altitude: Float(-500, 100000), // meters, Dead Sea to space
});

// ============================================================================
// Country/State codes
// ============================================================================

/**
 * ISO 3166-1 alpha-2 country code (US, GB, DE, etc.)
 */
export const CountryCodeAlpha2 = () => S(upper(2));

/**
 * ISO 3166-1 alpha-3 country code (USA, GBR, DEU, etc.)
 */
export const CountryCodeAlpha3 = () => S(upper(3));

/**
 * US state code (2 letters) - validated against actual state codes
 */
export const USStateCode = () => Regex(/^(A[KLRZ]|C[AOT]|D[CE]|FL|GA|HI|I[ADLN]|K[SY]|LA|M[ADEINOST]|N[CDEHJMVY]|O[HKR]|PA|RI|S[CD]|T[NX]|UT|V[AT]|W[AIVY])$/);

// ============================================================================
// Address schemas
// ============================================================================

/**
 * US street address
 */
export const USAddress = () => Struct({
  street1: UnicodeString(1, 100),
  street2: UnicodeString(0, 100),
  city: S(letters(1, 100)),
  state: USStateCode(),
  zipCode: USZipCode(),
});

/**
 * UK address
 */
export const UKAddress = () => Struct({
  street1: UnicodeString(1, 100),
  street2: UnicodeString(0, 100),
  city: S(letters(1, 100)),
  county: S(letters(0, 50)),
  postcode: UKPostcode(),
});

/**
 * Generic international address
 */
export const InternationalAddress = () => Struct({
  street1: UnicodeString(1, 200),
  street2: UnicodeString(0, 200),
  city: UnicodeString(1, 100),
  region: UnicodeString(0, 100),
  postalCode: PostalCode(),
  country: CountryCodeAlpha2(),
});

/**
 * Shipping address with recipient
 */
export const ShippingAddress = () => Struct({
  recipientName: UnicodeString(1, 100),
  company: UnicodeString(0, 100),
  street1: UnicodeString(1, 200),
  street2: UnicodeString(0, 200),
  city: UnicodeString(1, 100),
  region: UnicodeString(0, 100),
  postalCode: S(alphanumeric(1, 20)),
  country: CountryCodeAlpha2(),
  phone: S(chars('0-9 +()-', 0, 20)),
});

/**
 * Place with coordinates
 */
export const GeoLocation = () => Struct({
  name: UnicodeString(1, 200),
  address: UnicodeString(0, 500),
  coordinates: Coordinates(),
});
