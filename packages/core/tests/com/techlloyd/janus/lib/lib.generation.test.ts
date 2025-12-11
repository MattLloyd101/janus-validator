/**
 * Generation tests for the common validation patterns library
 * 
 * These tests verify that each validator can generate valid examples
 * using the Generator class.
 */

import { Generator } from '@/com/techlloyd/janus/Generator';
import { Validator } from '@/com/techlloyd/janus/Validator';
import { RNG } from '@/com/techlloyd/janus/RNG';

/**
 * Default RNG using Math.random
 */
class DefaultRNG implements RNG {
  random(): number {
    return Math.random();
  }
}

import {
  // Credentials
  Username, UsernameWithDots, Handle, Password, StrongPassword, PIN,
  JWT, APIKey, BearerToken,
  // Contact
  Email, StrictEmail, CorporateEmail, USPhone, InternationalPhone, E164Phone, UKPhone,
  TwitterHandle, InstagramHandle, LinkedInURL, ContactForm, FullContact,
  // Network
  URL, SimpleURL, SecureURL, WebSocketURL, FTPURL,
  Domain, Subdomain, Hostname,
  IPv4, IPv6, IPAddress, CIDR, PrivateIPv4,
  Port, WellKnownPort, RegisteredPort, DynamicPort,
  MACAddress, HostPort, ServerConfig,
  // Location
  USZipCode, UKPostcode, CanadianPostalCode, GermanPLZ, PostalCode,
  Latitude, Longitude, Coordinates, Coordinates3D,
  CountryCodeAlpha2, CountryCodeAlpha3, USStateCode,
  USAddress, UKAddress, InternationalAddress, ShippingAddress, GeoLocation,
  // Finance
  CreditCardNumber, VisaCard, MasterCard, AmexCard, CVV, CardExpiry, CreditCard,
  CurrencyCode, MoneyAmount, Price, Percentage, Money,
  USRoutingNumber, USBankAccountNumber, IBAN, SWIFT, USBankAccount,
  SSN, EIN, UKVAT, EUVAT,
  Transaction, PaymentMethod,
  // DateTime
  ISODate, ISODateTime, USDate, EUDate, Year, Month, DayOfMonth,
  Time24, Time24WithSeconds, Time12, Hour24, Hour12, Minute, Second,
  IANATimezone, UTCOffset,
  ISODuration, DurationMs, DurationSeconds,
  DateRange, DateTimeRange, ScheduledEvent, CronExpression,
  // Identifiers
  UUIDv4, UUID, UUIDNoDashes,
  Slug, Base64ID, NanoID, ShortID,
  IntegerID, ObjectID, SnowflakeID, CUID, ULID,
  SemVer, SemVerFull,
  MD5Hash, SHA1Hash, SHA256Hash, GitCommitHash,
  HexColor, HexColorAlpha, LanguageCode, LocaleCode,
} from '@/com/techlloyd/janus/lib';

/**
 * Helper function to test that a validator can generate valid values
 */
function testGeneration<T>(name: string, validator: Validator<T>, iterations: number = 100): void {
  const generator = new Generator(new DefaultRNG());
  
  for (let i = 0; i < iterations; i++) {
    const generated = generator.generate(validator);
    const result = validator.validate(generated);
    
    if (!result.valid) {
      throw new Error(
        `${name}: Generated value failed validation.\n` +
        `  Generated: ${JSON.stringify(generated)}\n` +
        `  Error: ${result.error}`
      );
    }
  }
}

describe('Lib Generation Tests', () => {
  describe('Credentials Generation', () => {
    it('Username generates valid usernames', () => {
      testGeneration('Username', Username());
    });

    it('UsernameWithDots generates valid usernames', () => {
      testGeneration('UsernameWithDots', UsernameWithDots());
    });

    it('Handle generates valid handles', () => {
      testGeneration('Handle', Handle());
    });

    it('Password generates valid passwords', () => {
      testGeneration('Password', Password());
    });

    it('StrongPassword generates valid strong passwords', () => {
      testGeneration('StrongPassword', StrongPassword());
    });

    it('PIN generates valid PINs', () => {
      testGeneration('PIN', PIN());
    });

    it('JWT generates valid JWT tokens', () => {
      testGeneration('JWT', JWT());
    });

    it('APIKey generates valid API keys', () => {
      testGeneration('APIKey', APIKey());
    });

    it('BearerToken generates valid bearer tokens', () => {
      testGeneration('BearerToken', BearerToken());
    });
  });

  describe('Contact Generation', () => {
    it('Email generates valid emails', () => {
      testGeneration('Email', Email());
    });

    it('StrictEmail generates valid strict emails', () => {
      testGeneration('StrictEmail', StrictEmail());
    });

    it('CorporateEmail generates valid corporate emails', () => {
      testGeneration('CorporateEmail', CorporateEmail());
    });

    it('USPhone generates valid US phones', () => {
      testGeneration('USPhone', USPhone());
    });

    it('InternationalPhone generates valid international phones', () => {
      testGeneration('InternationalPhone', InternationalPhone());
    });

    it('E164Phone generates valid E.164 phones', () => {
      testGeneration('E164Phone', E164Phone());
    });

    it('UKPhone generates valid UK phones', () => {
      testGeneration('UKPhone', UKPhone());
    });

    it('TwitterHandle generates valid Twitter handles', () => {
      testGeneration('TwitterHandle', TwitterHandle());
    });

    it('InstagramHandle generates valid Instagram handles', () => {
      testGeneration('InstagramHandle', InstagramHandle());
    });

    it('LinkedInURL generates valid LinkedIn URLs', () => {
      testGeneration('LinkedInURL', LinkedInURL());
    });

    it('ContactForm generates valid contact forms', () => {
      testGeneration('ContactForm', ContactForm());
    });

    it('FullContact generates valid full contacts', () => {
      testGeneration('FullContact', FullContact());
    });
  });

  describe('Network Generation', () => {
    it('URL generates valid URLs', () => {
      testGeneration('URL', URL());
    });

    it('SimpleURL generates valid simple URLs', () => {
      testGeneration('SimpleURL', SimpleURL());
    });

    it('SecureURL generates valid secure URLs', () => {
      testGeneration('SecureURL', SecureURL());
    });

    it('WebSocketURL generates valid WebSocket URLs', () => {
      testGeneration('WebSocketURL', WebSocketURL());
    });

    it('FTPURL generates valid FTP URLs', () => {
      testGeneration('FTPURL', FTPURL());
    });

    it('Domain generates valid domains', () => {
      testGeneration('Domain', Domain());
    });

    it('Subdomain generates valid subdomains', () => {
      testGeneration('Subdomain', Subdomain());
    });

    it('Hostname generates valid hostnames', () => {
      testGeneration('Hostname', Hostname());
    });

    it('IPv4 generates valid IPv4 addresses', () => {
      testGeneration('IPv4', IPv4());
    });

    it('IPv6 generates valid IPv6 addresses', () => {
      testGeneration('IPv6', IPv6());
    });

    it('IPAddress generates valid IP addresses', () => {
      testGeneration('IPAddress', IPAddress());
    });

    it('CIDR generates valid CIDR notation', () => {
      testGeneration('CIDR', CIDR());
    });

    it('PrivateIPv4 generates valid private IPv4 addresses', () => {
      testGeneration('PrivateIPv4', PrivateIPv4());
    });

    it('Port generates valid ports', () => {
      testGeneration('Port', Port());
    });

    it('WellKnownPort generates valid well-known ports', () => {
      testGeneration('WellKnownPort', WellKnownPort());
    });

    it('RegisteredPort generates valid registered ports', () => {
      testGeneration('RegisteredPort', RegisteredPort());
    });

    it('DynamicPort generates valid dynamic ports', () => {
      testGeneration('DynamicPort', DynamicPort());
    });

    it('MACAddress generates valid MAC addresses', () => {
      testGeneration('MACAddress', MACAddress());
    });

    it('HostPort generates valid host:port objects', () => {
      testGeneration('HostPort', HostPort());
    });

    it('ServerConfig generates valid server configs', () => {
      testGeneration('ServerConfig', ServerConfig());
    });
  });

  describe('Location Generation', () => {
    it('USZipCode generates valid US ZIP codes', () => {
      testGeneration('USZipCode', USZipCode());
    });

    it('UKPostcode generates valid UK postcodes', () => {
      testGeneration('UKPostcode', UKPostcode());
    });

    it('CanadianPostalCode generates valid Canadian postal codes', () => {
      testGeneration('CanadianPostalCode', CanadianPostalCode());
    });

    it('GermanPLZ generates valid German PLZ', () => {
      testGeneration('GermanPLZ', GermanPLZ());
    });

    it('PostalCode generates valid postal codes', () => {
      testGeneration('PostalCode', PostalCode());
    });

    it('Latitude generates valid latitudes', () => {
      testGeneration('Latitude', Latitude());
    });

    it('Longitude generates valid longitudes', () => {
      testGeneration('Longitude', Longitude());
    });

    it('Coordinates generates valid coordinates', () => {
      testGeneration('Coordinates', Coordinates());
    });

    it('Coordinates3D generates valid 3D coordinates', () => {
      testGeneration('Coordinates3D', Coordinates3D());
    });

    it('CountryCodeAlpha2 generates valid country codes', () => {
      testGeneration('CountryCodeAlpha2', CountryCodeAlpha2());
    });

    it('CountryCodeAlpha3 generates valid 3-letter country codes', () => {
      testGeneration('CountryCodeAlpha3', CountryCodeAlpha3());
    });

    it('USStateCode generates valid US state codes', () => {
      testGeneration('USStateCode', USStateCode());
    });

    it('USAddress generates valid US addresses', () => {
      testGeneration('USAddress', USAddress());
    });

    it('UKAddress generates valid UK addresses', () => {
      testGeneration('UKAddress', UKAddress());
    });

    it('InternationalAddress generates valid international addresses', () => {
      testGeneration('InternationalAddress', InternationalAddress());
    });

    it('ShippingAddress generates valid shipping addresses', () => {
      testGeneration('ShippingAddress', ShippingAddress());
    });

    it('GeoLocation generates valid geolocations', () => {
      testGeneration('GeoLocation', GeoLocation());
    });
  });

  describe('Finance Generation', () => {
    it('CreditCardNumber generates valid credit card numbers', () => {
      testGeneration('CreditCardNumber', CreditCardNumber());
    });

    it('VisaCard generates valid Visa cards', () => {
      testGeneration('VisaCard', VisaCard());
    });

    it('MasterCard generates valid MasterCards', () => {
      testGeneration('MasterCard', MasterCard());
    });

    it('AmexCard generates valid Amex cards', () => {
      testGeneration('AmexCard', AmexCard());
    });

    it('CVV generates valid CVVs', () => {
      testGeneration('CVV', CVV());
    });

    it('CardExpiry generates valid card expiries', () => {
      testGeneration('CardExpiry', CardExpiry());
    });

    it('CreditCard generates valid credit card objects', () => {
      testGeneration('CreditCard', CreditCard());
    });

    it('CurrencyCode generates valid currency codes', () => {
      testGeneration('CurrencyCode', CurrencyCode());
    });

    it('MoneyAmount generates valid money amounts', () => {
      testGeneration('MoneyAmount', MoneyAmount());
    });

    it('Price generates valid prices', () => {
      testGeneration('Price', Price());
    });

    it('Percentage generates valid percentages', () => {
      testGeneration('Percentage', Percentage());
    });

    it('Money generates valid money objects', () => {
      testGeneration('Money', Money());
    });

    it('USRoutingNumber generates valid routing numbers', () => {
      testGeneration('USRoutingNumber', USRoutingNumber());
    });

    it('USBankAccountNumber generates valid account numbers', () => {
      testGeneration('USBankAccountNumber', USBankAccountNumber());
    });

    it('IBAN generates valid IBANs', () => {
      testGeneration('IBAN', IBAN());
    });

    it('SWIFT generates valid SWIFT codes', () => {
      testGeneration('SWIFT', SWIFT());
    });

    it('USBankAccount generates valid US bank accounts', () => {
      testGeneration('USBankAccount', USBankAccount());
    });

    it('SSN generates valid SSNs', () => {
      testGeneration('SSN', SSN());
    });

    it('EIN generates valid EINs', () => {
      testGeneration('EIN', EIN());
    });

    it('UKVAT generates valid UK VAT numbers', () => {
      testGeneration('UKVAT', UKVAT());
    });

    it('EUVAT generates valid EU VAT numbers', () => {
      testGeneration('EUVAT', EUVAT());
    });

    it('Transaction generates valid transactions', () => {
      testGeneration('Transaction', Transaction());
    });

    it('PaymentMethod generates valid payment methods', () => {
      testGeneration('PaymentMethod', PaymentMethod());
    });
  });

  describe('DateTime Generation', () => {
    it('ISODate generates valid ISO dates', () => {
      testGeneration('ISODate', ISODate());
    });

    it('ISODateTime generates valid ISO datetimes', () => {
      testGeneration('ISODateTime', ISODateTime());
    });

    it('USDate generates valid US dates', () => {
      testGeneration('USDate', USDate());
    });

    it('EUDate generates valid EU dates', () => {
      testGeneration('EUDate', EUDate());
    });

    it('Year generates valid years', () => {
      testGeneration('Year', Year());
    });

    it('Month generates valid months', () => {
      testGeneration('Month', Month());
    });

    it('DayOfMonth generates valid days', () => {
      testGeneration('DayOfMonth', DayOfMonth());
    });

    it('Time24 generates valid 24-hour times', () => {
      testGeneration('Time24', Time24());
    });

    it('Time24WithSeconds generates valid times with seconds', () => {
      testGeneration('Time24WithSeconds', Time24WithSeconds());
    });

    it('Time12 generates valid 12-hour times', () => {
      testGeneration('Time12', Time12());
    });

    it('Hour24 generates valid 24-hour hours', () => {
      testGeneration('Hour24', Hour24());
    });

    it('Hour12 generates valid 12-hour hours', () => {
      testGeneration('Hour12', Hour12());
    });

    it('Minute generates valid minutes', () => {
      testGeneration('Minute', Minute());
    });

    it('Second generates valid seconds', () => {
      testGeneration('Second', Second());
    });

    it('IANATimezone generates valid IANA timezones', () => {
      testGeneration('IANATimezone', IANATimezone());
    });

    it('UTCOffset generates valid UTC offsets', () => {
      testGeneration('UTCOffset', UTCOffset());
    });

    it('ISODuration generates valid ISO durations', () => {
      testGeneration('ISODuration', ISODuration());
    });

    it('DurationMs generates valid durations in ms', () => {
      testGeneration('DurationMs', DurationMs());
    });

    it('DurationSeconds generates valid durations in seconds', () => {
      testGeneration('DurationSeconds', DurationSeconds());
    });

    it('DateRange generates valid date ranges', () => {
      testGeneration('DateRange', DateRange());
    });

    it('DateTimeRange generates valid datetime ranges', () => {
      testGeneration('DateTimeRange', DateTimeRange());
    });

    it('ScheduledEvent generates valid scheduled events', () => {
      testGeneration('ScheduledEvent', ScheduledEvent());
    });

    it('CronExpression generates valid cron expressions', () => {
      testGeneration('CronExpression', CronExpression());
    });
  });

  describe('Identifiers Generation', () => {
    it('UUIDv4 generates valid v4 UUIDs', () => {
      testGeneration('UUIDv4', UUIDv4());
    });

    it('UUID generates valid UUIDs', () => {
      testGeneration('UUID', UUID());
    });

    it('UUIDNoDashes generates valid UUIDs without dashes', () => {
      testGeneration('UUIDNoDashes', UUIDNoDashes());
    });

    it('Slug generates valid slugs', () => {
      testGeneration('Slug', Slug());
    });

    it('Base64ID generates valid base64 IDs', () => {
      testGeneration('Base64ID', Base64ID());
    });

    it('NanoID generates valid nano IDs', () => {
      testGeneration('NanoID', NanoID());
    });

    it('ShortID generates valid short IDs', () => {
      testGeneration('ShortID', ShortID());
    });

    it('IntegerID generates valid integer IDs', () => {
      testGeneration('IntegerID', IntegerID());
    });

    it('ObjectID generates valid MongoDB ObjectIds', () => {
      testGeneration('ObjectID', ObjectID());
    });

    it('SnowflakeID generates valid Snowflake IDs', () => {
      testGeneration('SnowflakeID', SnowflakeID());
    });

    it('CUID generates valid CUIDs', () => {
      testGeneration('CUID', CUID());
    });

    it('ULID generates valid ULIDs', () => {
      testGeneration('ULID', ULID());
    });

    it('SemVer generates valid semantic versions', () => {
      testGeneration('SemVer', SemVer());
    });

    it('SemVerFull generates valid full semantic versions', () => {
      testGeneration('SemVerFull', SemVerFull());
    });

    it('MD5Hash generates valid MD5 hashes', () => {
      testGeneration('MD5Hash', MD5Hash());
    });

    it('SHA1Hash generates valid SHA-1 hashes', () => {
      testGeneration('SHA1Hash', SHA1Hash());
    });

    it('SHA256Hash generates valid SHA-256 hashes', () => {
      testGeneration('SHA256Hash', SHA256Hash());
    });

    it('GitCommitHash generates valid Git commit hashes', () => {
      testGeneration('GitCommitHash', GitCommitHash());
    });

    it('HexColor generates valid hex colors', () => {
      testGeneration('HexColor', HexColor());
    });

    it('HexColorAlpha generates valid hex colors with alpha', () => {
      testGeneration('HexColorAlpha', HexColorAlpha());
    });

    it('LanguageCode generates valid language codes', () => {
      testGeneration('LanguageCode', LanguageCode());
    });

    it('LocaleCode generates valid locale codes', () => {
      testGeneration('LocaleCode', LocaleCode());
    });
  });
});

