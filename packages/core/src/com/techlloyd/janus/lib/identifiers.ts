/**
 * Identifier validators - UUIDs, slugs, IDs
 */

import { S, I, R, O, Or, digits, hex, alphanumeric, lower, chars, caseInsensitive } from '../DSL';

// ============================================================================
// UUIDs
// ============================================================================

/**
 * UUID v4 format: xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx
 * Version 4 (random), variant 1 (8, 9, a, b)
 */
export const UUIDv4 = () => caseInsensitive(S(
  hex(8), '-', hex(4), '-', '4', hex(3), '-', chars('89ab', 1), hex(3), '-', hex(12)
));

/**
 * Any UUID format (v1-v5)
 * Version 1-5, variant 1 (8, 9, a, b)
 */
export const UUID = () => caseInsensitive(S(
  hex(8), '-', hex(4), '-', chars('12345', 1), hex(3), '-', chars('89ab', 1), hex(3), '-', hex(12)
));

/**
 * UUID without dashes (32 hex chars)
 */
export const UUIDNoDashes = () => S(hex(32));

/**
 * Simple UUID-like format (for generation, no version constraints)
 */
export const UUIDSimple = () => S(
  hex(8), '-', hex(4), '-', hex(4), '-', hex(4), '-', hex(12)
);

// ============================================================================
// Slugs and URL-safe IDs
// ============================================================================

/**
 * URL slug (lowercase letters, numbers, hyphens)
 */
export const Slug = () => R(/^[a-z0-9]+(-[a-z0-9]+)*$/);

/**
 * URL-safe base64 ID
 */
export const Base64ID = () => S(chars('A-Za-z0-9_-', 1, 100));

/**
 * Nanoid-style ID (21 chars)
 */
export const NanoID = () => S(chars('A-Za-z0-9_-', 21));

/**
 * Short ID (6-12 alphanumeric)
 */
export const ShortID = () => S(alphanumeric(6, 12));

// ============================================================================
// Database IDs
// ============================================================================

/**
 * Positive integer ID
 */
export const IntegerID = () => I(1, Number.MAX_SAFE_INTEGER);

/**
 * MongoDB ObjectId (24 hex chars)
 */
export const ObjectID = () => S(hex(24));

/**
 * Snowflake ID (Twitter/Discord style, 17-19 digits)
 */
export const SnowflakeID = () => S(digits(17, 19));

/**
 * CUID (collision-resistant unique ID): c + 24 lowercase alphanumeric
 */
export const CUID = () => S('c', lower(24));

/**
 * ULID (Universally Unique Lexicographically Sortable Identifier)
 * Uses Crockford's base32: 0-9, A-H, J-N, P-T, V-Z (no I, L, O, U)
 */
export const ULID = () => S(chars('0-9A-HJKMNP-TV-Z', 26));

// ============================================================================
// Semantic versioning
// ============================================================================

/**
 * Version parts for composition
 */
const versionParts = () => [digits(1, 5), '.', digits(1, 5), '.', digits(1, 5)] as const;

/**
 * Semantic version (MAJOR.MINOR.PATCH)
 */
export const SemVer = () => S(...versionParts());

/**
 * Semantic version with optional prerelease and/or build metadata
 * Composed from version parts with optional suffixes
 */
export const SemVerFull = () => Or(
  S(...versionParts()),                                           // X.Y.Z
  S(...versionParts(), '-', alphanumeric(1, 20)),                 // X.Y.Z-prerelease
  S(...versionParts(), '+', alphanumeric(1, 20)),                 // X.Y.Z+build
  S(...versionParts(), '-', alphanumeric(1, 20), '+', alphanumeric(1, 20)) // X.Y.Z-prerelease+build
);

// ============================================================================
// Hashes
// ============================================================================

/**
 * MD5 hash (32 hex chars)
 */
export const MD5Hash = () => S(hex(32));

/**
 * SHA-1 hash (40 hex chars)
 */
export const SHA1Hash = () => S(hex(40));

/**
 * SHA-256 hash (64 hex chars)
 */
export const SHA256Hash = () => S(hex(64));

/**
 * Git commit hash (short: 7, full: 40)
 */
export const GitCommitHash = () => S(hex(7, 40));

// ============================================================================
// Codes
// ============================================================================

/**
 * Hex color code: #RGB (case-insensitive)
 */
export const HexColor3 = () => caseInsensitive(S('#', hex(3)));

/**
 * Hex color code: #RGBA (case-insensitive)
 */
export const HexColor4 = () => caseInsensitive(S('#', hex(4)));

/**
 * Hex color code: #RRGGBB (case-insensitive)
 */
export const HexColor6 = () => caseInsensitive(S('#', hex(6)));

/**
 * Hex color code: #RRGGBBAA (case-insensitive)
 */
export const HexColor8 = () => caseInsensitive(S('#', hex(8)));

/**
 * Hex color code (#RGB or #RRGGBB)
 */
export const HexColor = () => Or(HexColor3(), HexColor6());

/**
 * Hex color with alpha (#RGB, #RGBA, #RRGGBB, #RRGGBBAA)
 */
export const HexColorAlpha = () => Or(HexColor3(), HexColor4(), HexColor6(), HexColor8());

/**
 * Language code (ISO 639-1, e.g., en, fr, de)
 */
export const LanguageCode = () => S(lower(2));

/**
 * Locale code (e.g., en-US, fr-FR)
 */
export const LocaleCode = () => R(/^[a-z]{2}(-[A-Z]{2})?$/);

// ============================================================================
// Identifiable entities
// ============================================================================

/**
 * Entity with ID
 */
export const WithID = <T extends object>(schema: T) => O({
  id: Or(UUIDv4(), IntegerID()),
  ...schema,
});

/**
 * Entity with timestamps
 */
export const WithTimestamps = <T extends object>(schema: T) => O({
  ...schema,
  createdAt: Or(ISOTimestamp(), I(0, Number.MAX_SAFE_INTEGER)),
  updatedAt: Or(ISOTimestamp(), I(0, Number.MAX_SAFE_INTEGER)),
});

/**
 * ISO timestamp pattern
 */
const ISOTimestamp = () => S(
  digits(4), '-', digits(2), '-', digits(2),
  'T',
  digits(2), ':', digits(2), ':', digits(2)
);
