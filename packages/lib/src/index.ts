/**
 * @janus-validator/lib
 * 
 * Common validation patterns library for Janus Validator.
 * 
 * All validators are domain-based, enabling:
 * - Valid value generation (round-trip testing)
 * - Schema evolution via encapsulates()
 * - Set operations (union, intersect, subtract)
 * 
 * @example
 * ```typescript
 * import { Email, UUIDv4, USPhone, ISODate } from '@janus-validator/lib';
 * import { O } from '@janus-validator/dsl';
 * import { Generator } from '@janus-validator/core';
 * 
 * const User = O({
 *   id: UUIDv4(),
 *   email: Email(),
 *   phone: USPhone(),
 *   createdAt: ISODate(),
 * });
 * 
 * // Validate
 * const result = User.validate(input);
 * 
 * // Generate valid test data
 * const generator = new Generator({ random: Math.random });
 * const testUser = generator.generate(User.domain);
 * ```
 */

// Network validators
export {
  URL,
  SimpleURL,
  SecureURL,
  WebSocketURL,
  FTPURL,
  Domain,
  Subdomain,
  Hostname,
  IPv4,
  IPv4Simple,
  IPv6,
  IPv6Full,
  IPAddress,
  CIDR,
  PrivateIPv4,
  Port,
  WellKnownPort,
  RegisteredPort,
  DynamicPort,
  MACAddressColon,
  MACAddressHyphen,
  MACAddress,
  HostPort,
  ServerConfig,
} from './validators/network';

// Identifier validators
export {
  UUID,
  UUIDv4,
  UUIDNoDashes,
  UUIDSimple,
  Slug,
  Base64ID,
  NanoID,
  ShortID,
  IntegerID,
  ObjectID,
  SnowflakeID,
  CUID,
  ULID,
  SemVer,
  SemVerFull,
  MD5Hash,
  SHA1Hash,
  SHA256Hash,
  GitCommitHash,
  HexColor,
  HexColor3,
  HexColor4,
  HexColor6,
  HexColor8,
  HexColorAlpha,
  LanguageCode,
  LocaleCode,
  WithID,
  WithTimestamps,
} from './validators/identifiers';

// Contact validators
export {
  Email,
  StrictEmail,
  CorporateEmail,
  USPhoneFormatted,
  USPhone,
  InternationalPhone,
  E164Phone,
  UKPhone,
  TwitterHandle,
  InstagramHandle,
  LinkedInURL,
  ContactForm,
  FullContact,
} from './validators/contact';

// Credential validators
export {
  Username,
  UsernameWithDots,
  Handle,
  Password,
  PIN,
  PIN4,
  PIN6,
  JWT,
  APIKey,
  BearerToken,
} from './validators/credentials';

// DateTime validators
export {
  ISODate,
  ISODateTime,
  USDate,
  EUDate,
  Year,
  Month,
  DayOfMonth,
  Time24,
  Time24WithSeconds,
  Time12,
  Hour24,
  Hour12,
  Minute,
  Second,
  IANATimezone,
  UTCOffset,
  ISODuration,
  DurationMs,
  DurationSeconds,
  DateRange,
  DateTimeRange,
  ScheduledEvent,
  CronExpression,
} from './validators/datetime';

// Financial validators
export {
  CreditCardNumber,
  VisaCard,
  MasterCard,
  AmexCard,
  CVV,
  CardExpiryShort,
  CardExpiryLong,
  CardExpiry,
  CreditCard,
  CurrencyCode,
  MoneyAmount,
  Price,
  Percentage,
  Money,
  USRoutingNumber,
  USBankAccountNumber,
  IBAN,
  SWIFT,
  USBankAccount,
  SSNFormatted,
  SSN,
  EINFormatted,
  EIN,
  UKVAT,
  EUVAT,
  Transaction,
  PaymentMethod,
} from './validators/finance';

// Location validators
export {
  USZip5,
  USZipPlus4,
  USZipCode,
  UKPostcode,
  CanadianPostalCode,
  GermanPLZ,
  PostalCode,
  Latitude,
  Longitude,
  Coordinates,
  Coordinates3D,
  CountryCodeAlpha2,
  CountryCodeAlpha3,
  USStateCode,
  USAddress,
  UKAddress,
  InternationalAddress,
  ShippingAddress,
  GeoLocation,
} from './validators/location';

// Realistic presets (generation overrides)
export {
  FirstName,
  LastName,
  FullName,
  RealisticUsername,
  RealisticEmail,
  CorporateEmailPreset,
  RealisticStreetAddress,
  RealisticCity,
  RealisticState,
  RealisticZipCode,
  RealisticUSPhone,
  CompanyName,
  ProductName,
  LoremIpsum,
  RecentDate,
  FutureDate,
  RealisticPrice,
} from './validators/presets';

// String utility validators
export {
  StartsWith,
  EndsWith,
  Contains,
  StartsWithPattern,
  EndsWithPattern,
} from './validators/strings';
