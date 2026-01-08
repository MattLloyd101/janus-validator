/**
 * Comprehensive tests for @janus-validator/lib validators
 * 
 * These tests verify that:
 * 1. Validators validate correct values
 * 2. Validators reject invalid values
 * 3. Domains generate valid values (round-trip)
 */

import { Generator } from '@janus-validator/core';
import {
  // Network
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
  
  // Identifiers
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
  
  // Contact
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
  
  // Credentials
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
  
  // DateTime
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
  
  // Financial
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
  
  // Location
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
  
  // Presets
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
} from '../src';

describe('@janus-validator/lib', () => {
  const generator = new Generator({ random: Math.random });

  // Helper for round-trip testing
  const testRoundTrip = (validatorFn: () => any, iterations = 5) => {
    for (let i = 0; i < iterations; i++) {
      const validator = validatorFn();
      const generated = generator.generate(validator.domain);
      const result = validator.validate(generated);
      expect(result.valid).toBe(true);
    }
  };

  // ============================================================================
  // Network validators
  // ============================================================================

  describe('Network validators', () => {
    describe('URL', () => {
      it('validates valid URLs', () => {
        expect(URL().validate('http://example.com').valid).toBe(true);
        expect(URL().validate('https://example.com/path').valid).toBe(true);
        expect(URL().validate('https://example.com:8080/path?query=1').valid).toBe(true);
        expect(URL().validate('https://sub.example.com/path#anchor').valid).toBe(true);
      });

      it('rejects invalid URLs', () => {
        expect(URL().validate('not-a-url').valid).toBe(false);
        expect(URL().validate('ftp://example.com').valid).toBe(false);
      });
    });

    describe('SimpleURL', () => {
      it('validates simple URLs', () => {
        expect(SimpleURL().validate('http://example.com').valid).toBe(true);
        expect(SimpleURL().validate('https://example.com/path?query=1').valid).toBe(true);
      });

      it('rejects non-HTTP URLs', () => {
        expect(SimpleURL().validate('ftp://example.com').valid).toBe(false);
      });
    });

    describe('SecureURL', () => {
      it('validates HTTPS URLs only', () => {
        expect(SecureURL().validate('https://example.com').valid).toBe(true);
        expect(SecureURL().validate('https://example.com/path').valid).toBe(true);
      });

      it('rejects HTTP URLs', () => {
        expect(SecureURL().validate('http://example.com').valid).toBe(false);
      });
    });

    describe('WebSocketURL', () => {
      it('validates WebSocket URLs', () => {
        expect(WebSocketURL().validate('ws://example.com').valid).toBe(true);
        expect(WebSocketURL().validate('wss://example.com/socket').valid).toBe(true);
      });

      it('rejects non-WebSocket URLs', () => {
        expect(WebSocketURL().validate('http://example.com').valid).toBe(false);
      });
    });

    describe('FTPURL', () => {
      it('validates FTP URLs', () => {
        expect(FTPURL().validate('ftp://ftp.example.com').valid).toBe(true);
        expect(FTPURL().validate('ftps://ftp.example.com/files').valid).toBe(true);
      });

      it('rejects non-FTP URLs', () => {
        expect(FTPURL().validate('http://example.com').valid).toBe(false);
      });
    });

    describe('Domain', () => {
      it('validates domain names', () => {
        expect(Domain().validate('example.com').valid).toBe(true);
        expect(Domain().validate('sub.example.com').valid).toBe(true);
        expect(Domain().validate('deep.sub.example.co.uk').valid).toBe(true);
      });

      it('rejects invalid domains', () => {
        expect(Domain().validate('example').valid).toBe(false);
        expect(Domain().validate('-example.com').valid).toBe(false);
      });
    });

    describe('Subdomain', () => {
      it('generates valid subdomains (round-trip)', () => {
        testRoundTrip(Subdomain);
      });
    });

    describe('Hostname', () => {
      it('validates hostnames (domain or IP)', () => {
        expect(Hostname().validate('example.com').valid).toBe(true);
        expect(Hostname().validate('192.168.1.1').valid).toBe(true);
      });
    });

    describe('IPv4', () => {
      it('validates valid IPv4 addresses', () => {
        expect(IPv4().validate('192.168.1.1').valid).toBe(true);
        expect(IPv4().validate('0.0.0.0').valid).toBe(true);
        expect(IPv4().validate('255.255.255.255').valid).toBe(true);
        expect(IPv4().validate('10.0.0.1').valid).toBe(true);
      });

      it('rejects invalid IPv4 addresses', () => {
        expect(IPv4().validate('256.0.0.0').valid).toBe(false);
        expect(IPv4().validate('192.168.1').valid).toBe(false);
        expect(IPv4().validate('abc.def.ghi.jkl').valid).toBe(false);
      });
    });

    describe('IPv4Simple', () => {
      it('generates valid simple IPv4 (round-trip)', () => {
        testRoundTrip(IPv4Simple);
      });
    });

    describe('IPv6', () => {
      it('validates IPv6 addresses', () => {
        expect(IPv6().validate('2001:0db8:85a3:0000:0000:8a2e:0370:7334').valid).toBe(true);
        expect(IPv6().validate('::1').valid).toBe(true);
        expect(IPv6().validate('fe80::').valid).toBe(true);
      });

      it('rejects invalid IPv6', () => {
        expect(IPv6().validate('invalid').valid).toBe(false);
      });
    });

    describe('IPv6Full', () => {
      it('generates valid full IPv6 (round-trip)', () => {
        testRoundTrip(IPv6Full);
      });
    });

    describe('IPAddress', () => {
      it('validates IPv4 or IPv6', () => {
        expect(IPAddress().validate('192.168.1.1').valid).toBe(true);
        expect(IPAddress().validate('::1').valid).toBe(true);
      });
    });

    describe('CIDR', () => {
      it('validates CIDR notation', () => {
        expect(CIDR().validate('192.168.1.0/24').valid).toBe(true);
        expect(CIDR().validate('10.0.0.0/8').valid).toBe(true);
        expect(CIDR().validate('0.0.0.0/0').valid).toBe(true);
      });

      it('rejects invalid CIDR', () => {
        expect(CIDR().validate('192.168.1.0/33').valid).toBe(false);
      });
    });

    describe('PrivateIPv4', () => {
      it('validates private IP ranges', () => {
        expect(PrivateIPv4().validate('10.0.0.1').valid).toBe(true);
        expect(PrivateIPv4().validate('172.16.0.1').valid).toBe(true);
        expect(PrivateIPv4().validate('192.168.1.1').valid).toBe(true);
      });
    });

    describe('Port', () => {
      it('validates valid ports', () => {
        expect(Port().validate(80).valid).toBe(true);
        expect(Port().validate(443).valid).toBe(true);
        expect(Port().validate(65535).valid).toBe(true);
        expect(Port().validate(1).valid).toBe(true);
      });

      it('rejects invalid ports', () => {
        expect(Port().validate(0).valid).toBe(false);
        expect(Port().validate(65536).valid).toBe(false);
        expect(Port().validate(-1).valid).toBe(false);
      });
    });

    describe('WellKnownPort', () => {
      it('validates well-known ports', () => {
        expect(WellKnownPort().validate(80).valid).toBe(true);
        expect(WellKnownPort().validate(443).valid).toBe(true);
        expect(WellKnownPort().validate(1).valid).toBe(true);
        expect(WellKnownPort().validate(1023).valid).toBe(true);
      });

      it('rejects ports outside range', () => {
        expect(WellKnownPort().validate(1024).valid).toBe(false);
      });
    });

    describe('RegisteredPort', () => {
      it('validates registered ports', () => {
        expect(RegisteredPort().validate(1024).valid).toBe(true);
        expect(RegisteredPort().validate(8080).valid).toBe(true);
        expect(RegisteredPort().validate(49151).valid).toBe(true);
      });

      it('rejects ports outside range', () => {
        expect(RegisteredPort().validate(1023).valid).toBe(false);
        expect(RegisteredPort().validate(49152).valid).toBe(false);
      });
    });

    describe('DynamicPort', () => {
      it('validates dynamic ports', () => {
        expect(DynamicPort().validate(49152).valid).toBe(true);
        expect(DynamicPort().validate(65535).valid).toBe(true);
      });

      it('rejects ports outside range', () => {
        expect(DynamicPort().validate(49151).valid).toBe(false);
      });
    });

    describe('MACAddressColon', () => {
      it('validates MAC with colons', () => {
        expect(MACAddressColon().validate('00:1A:2B:3C:4D:5E').valid).toBe(true);
        expect(MACAddressColon().validate('aa:bb:cc:dd:ee:ff').valid).toBe(true);
      });
    });

    describe('MACAddressHyphen', () => {
      it('validates MAC with hyphens', () => {
        expect(MACAddressHyphen().validate('00-1A-2B-3C-4D-5E').valid).toBe(true);
      });
    });

    describe('MACAddress', () => {
      it('validates either MAC format', () => {
        expect(MACAddress().validate('00:1A:2B:3C:4D:5E').valid).toBe(true);
        expect(MACAddress().validate('00-1A-2B-3C-4D-5E').valid).toBe(true);
      });
    });

    describe('HostPort', () => {
      it('validates host:port struct', () => {
        expect(HostPort().validate({ host: 'example.com', port: 8080 }).valid).toBe(true);
        expect(HostPort().validate({ host: '192.168.1.1', port: 443 }).valid).toBe(true);
      });
    });

    describe('ServerConfig', () => {
      it('validates server config', () => {
        expect(ServerConfig().validate({ 
          host: 'example.com', 
          port: 443, 
          protocol: 'https' 
        }).valid).toBe(true);
      });

      it('generates valid config (round-trip)', () => {
        testRoundTrip(ServerConfig);
      });
    });
  });

  // ============================================================================
  // Identifier validators
  // ============================================================================

  describe('Identifier validators', () => {
    describe('UUID', () => {
      it('validates any UUID version', () => {
        expect(UUID().validate('550e8400-e29b-11d4-a716-446655440000').valid).toBe(true); // v1
        expect(UUID().validate('550e8400-e29b-41d4-a716-446655440000').valid).toBe(true); // v4
      });

      it('generates valid UUIDs (round-trip)', () => {
        testRoundTrip(UUID);
      });
    });

    describe('UUIDv4', () => {
      it('validates valid UUIDv4', () => {
        expect(UUIDv4().validate('550e8400-e29b-41d4-a716-446655440000').valid).toBe(true);
        expect(UUIDv4().validate('550E8400-E29B-41D4-A716-446655440000').valid).toBe(true);
      });

      it('rejects invalid UUIDs', () => {
        expect(UUIDv4().validate('not-a-uuid').valid).toBe(false);
        expect(UUIDv4().validate('550e8400-e29b-21d4-a716-446655440000').valid).toBe(false);
      });

      it('generates valid UUIDs (round-trip)', () => {
        testRoundTrip(UUIDv4);
      });
    });

    describe('UUIDNoDashes', () => {
      it('validates UUID without dashes', () => {
        expect(UUIDNoDashes().validate('550e8400e29b41d4a716446655440000').valid).toBe(true);
      });

      it('generates valid (round-trip)', () => {
        testRoundTrip(UUIDNoDashes);
      });
    });

    describe('UUIDSimple', () => {
      it('generates valid simple UUIDs (round-trip)', () => {
        testRoundTrip(UUIDSimple);
      });
    });

    describe('Slug', () => {
      it('validates valid slugs', () => {
        expect(Slug().validate('my-article').valid).toBe(true);
        expect(Slug().validate('hello-world-123').valid).toBe(true);
        expect(Slug().validate('test').valid).toBe(true);
      });

      it('rejects invalid slugs', () => {
        expect(Slug().validate('My-Article').valid).toBe(false);
        expect(Slug().validate('hello_world').valid).toBe(false);
        expect(Slug().validate('-invalid').valid).toBe(false);
      });
    });

    describe('Base64ID', () => {
      it('generates valid base64 IDs (round-trip)', () => {
        testRoundTrip(Base64ID);
      });
    });

    describe('NanoID', () => {
      it('generates valid 21-char IDs (round-trip)', () => {
        for (let i = 0; i < 5; i++) {
          const generated = generator.generate(NanoID().domain);
          expect(generated.length).toBe(21);
          expect(NanoID().validate(generated).valid).toBe(true);
        }
      });
    });

    describe('ShortID', () => {
      it('generates valid short IDs (round-trip)', () => {
        testRoundTrip(ShortID);
      });
    });

    describe('IntegerID', () => {
      it('validates positive integers', () => {
        expect(IntegerID().validate(1).valid).toBe(true);
        expect(IntegerID().validate(999999).valid).toBe(true);
      });

      it('rejects non-positive', () => {
        expect(IntegerID().validate(0).valid).toBe(false);
        expect(IntegerID().validate(-1).valid).toBe(false);
      });
    });

    describe('ObjectID', () => {
      it('generates valid 24-char hex IDs (round-trip)', () => {
        for (let i = 0; i < 5; i++) {
          const generated = generator.generate(ObjectID().domain);
          expect(generated.length).toBe(24);
          expect(ObjectID().validate(generated).valid).toBe(true);
        }
      });
    });

    describe('SnowflakeID', () => {
      it('generates valid snowflake IDs (round-trip)', () => {
        testRoundTrip(SnowflakeID);
      });
    });

    describe('CUID', () => {
      it('generates valid CUIDs starting with c (round-trip)', () => {
        for (let i = 0; i < 5; i++) {
          const generated = generator.generate(CUID().domain);
          expect(generated.startsWith('c')).toBe(true);
          expect(CUID().validate(generated).valid).toBe(true);
        }
      });
    });

    describe('ULID', () => {
      it('generates valid 26-char ULIDs (round-trip)', () => {
        for (let i = 0; i < 5; i++) {
          const generated = generator.generate(ULID().domain);
          expect(generated.length).toBe(26);
          expect(ULID().validate(generated).valid).toBe(true);
        }
      });
    });

    describe('SemVer', () => {
      it('validates semantic versions', () => {
        expect(SemVer().validate('1.0.0').valid).toBe(true);
        expect(SemVer().validate('12.34.56').valid).toBe(true);
      });

      it('generates valid versions (round-trip)', () => {
        testRoundTrip(SemVer);
      });
    });

    describe('SemVerFull', () => {
      it('validates full semantic versions', () => {
        expect(SemVerFull().validate('1.0.0').valid).toBe(true);
        expect(SemVerFull().validate('1.0.0-alpha').valid).toBe(true);
        expect(SemVerFull().validate('1.0.0+build').valid).toBe(true);
        expect(SemVerFull().validate('1.0.0-beta+build123').valid).toBe(true);
      });

      it('generates valid versions (round-trip)', () => {
        testRoundTrip(SemVerFull);
      });
    });

    describe('MD5Hash', () => {
      it('validates 32-char hex hashes', () => {
        expect(MD5Hash().validate('d41d8cd98f00b204e9800998ecf8427e').valid).toBe(true);
      });

      it('generates valid hashes (round-trip)', () => {
        testRoundTrip(MD5Hash);
      });
    });

    describe('SHA1Hash', () => {
      it('validates 40-char hex hashes', () => {
        expect(SHA1Hash().validate('da39a3ee5e6b4b0d3255bfef95601890afd80709').valid).toBe(true);
      });

      it('generates valid hashes (round-trip)', () => {
        testRoundTrip(SHA1Hash);
      });
    });

    describe('SHA256Hash', () => {
      it('validates 64-char hex hashes', () => {
        const hash = 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855';
        expect(SHA256Hash().validate(hash).valid).toBe(true);
      });

      it('generates valid hashes (round-trip)', () => {
        testRoundTrip(SHA256Hash);
      });
    });

    describe('GitCommitHash', () => {
      it('validates git commit hashes (short and full)', () => {
        expect(GitCommitHash().validate('abc1234').valid).toBe(true);
        expect(GitCommitHash().validate('da39a3ee5e6b4b0d3255bfef95601890afd80709').valid).toBe(true);
      });

      it('generates valid hashes (round-trip)', () => {
        testRoundTrip(GitCommitHash);
      });
    });

    describe('HexColor3', () => {
      it('validates 3-char hex colors', () => {
        expect(HexColor3().validate('#fff').valid).toBe(true);
        expect(HexColor3().validate('#ABC').valid).toBe(true);
      });

      it('generates valid colors (round-trip)', () => {
        testRoundTrip(HexColor3);
      });
    });

    describe('HexColor4', () => {
      it('validates 4-char hex colors', () => {
        expect(HexColor4().validate('#ffff').valid).toBe(true);
      });

      it('generates valid colors (round-trip)', () => {
        testRoundTrip(HexColor4);
      });
    });

    describe('HexColor6', () => {
      it('validates hex colors', () => {
        expect(HexColor6().validate('#ffffff').valid).toBe(true);
        expect(HexColor6().validate('#AABBCC').valid).toBe(true);
        expect(HexColor6().validate('#123456').valid).toBe(true);
      });

      it('rejects invalid hex colors', () => {
        expect(HexColor6().validate('#fff').valid).toBe(false);
        expect(HexColor6().validate('ffffff').valid).toBe(false);
      });

      it('generates valid colors (round-trip)', () => {
        testRoundTrip(HexColor6);
      });
    });

    describe('HexColor8', () => {
      it('validates 8-char hex colors', () => {
        expect(HexColor8().validate('#ffffffff').valid).toBe(true);
      });

      it('generates valid colors (round-trip)', () => {
        testRoundTrip(HexColor8);
      });
    });

    describe('HexColor', () => {
      it('validates 3 or 6 char hex colors', () => {
        expect(HexColor().validate('#fff').valid).toBe(true);
        expect(HexColor().validate('#ffffff').valid).toBe(true);
      });
    });

    describe('HexColorAlpha', () => {
      it('validates any hex color format', () => {
        expect(HexColorAlpha().validate('#fff').valid).toBe(true);
        expect(HexColorAlpha().validate('#ffff').valid).toBe(true);
        expect(HexColorAlpha().validate('#ffffff').valid).toBe(true);
        expect(HexColorAlpha().validate('#ffffffff').valid).toBe(true);
      });
    });

    describe('LanguageCode', () => {
      it('generates valid 2-letter codes (round-trip)', () => {
        testRoundTrip(LanguageCode);
      });
    });

    describe('LocaleCode', () => {
      it('validates locale codes', () => {
        expect(LocaleCode().validate('en').valid).toBe(true);
        expect(LocaleCode().validate('en-US').valid).toBe(true);
        expect(LocaleCode().validate('fr-FR').valid).toBe(true);
      });
    });

    describe('WithID', () => {
      it('adds ID to schema', () => {
        const schema = WithID({ name: Username() });
        expect(schema.validate({ id: '550e8400-e29b-41d4-a716-446655440000', name: 'alice' }).valid).toBe(true);
        expect(schema.validate({ id: 123, name: 'alice' }).valid).toBe(true);
      });
    });

    describe('WithTimestamps', () => {
      it('adds timestamps to schema', () => {
        const schema = WithTimestamps({ name: Username() });
        const valid = schema.validate({ 
          name: 'alice',
          createdAt: '2024-01-15T10:30:00',
          updatedAt: '2024-01-15T10:30:00'
        });
        expect(valid.valid).toBe(true);
      });
    });
  });

  // ============================================================================
  // Contact validators
  // ============================================================================

  describe('Contact validators', () => {
    describe('Email', () => {
      it('validates valid emails', () => {
        expect(Email().validate('user@example.com').valid).toBe(true);
        expect(Email().validate('user.name@example.co.uk').valid).toBe(true);
        expect(Email().validate('user+tag@example.com').valid).toBe(true);
      });

      it('rejects invalid emails', () => {
        expect(Email().validate('not-an-email').valid).toBe(false);
        expect(Email().validate('@example.com').valid).toBe(false);
        expect(Email().validate('user@').valid).toBe(false);
      });
    });

    describe('StrictEmail', () => {
      it('validates emails with common TLDs', () => {
        expect(StrictEmail().validate('user@example.com').valid).toBe(true);
        expect(StrictEmail().validate('user@example.org').valid).toBe(true);
        expect(StrictEmail().validate('user@example.io').valid).toBe(true);
      });
    });

    describe('CorporateEmail', () => {
      it('generates valid corporate emails (round-trip)', () => {
        for (let i = 0; i < 5; i++) {
          const generated = generator.generate(CorporateEmail().domain);
          expect(Email().validate(generated).valid).toBe(true);
        }
      });
    });

    describe('USPhoneFormatted', () => {
      it('generates valid formatted US phones (round-trip)', () => {
        testRoundTrip(USPhoneFormatted);
      });
    });

    describe('USPhone', () => {
      it('validates US phone numbers', () => {
        expect(USPhone().validate('(555) 123-4567').valid).toBe(true);
        expect(USPhone().validate('555-123-4567').valid).toBe(true);
        expect(USPhone().validate('555.123.4567').valid).toBe(true);
      });

      it('rejects invalid phone numbers', () => {
        expect(USPhone().validate('123').valid).toBe(false);
        expect(USPhone().validate('not-a-phone').valid).toBe(false);
      });
    });

    describe('InternationalPhone', () => {
      it('validates international phones', () => {
        expect(InternationalPhone().validate('+1 555 123 4567').valid).toBe(true);
        expect(InternationalPhone().validate('+44 20 7123 4567').valid).toBe(true);
      });
    });

    describe('E164Phone', () => {
      it('validates E.164 format', () => {
        expect(E164Phone().validate('+15551234567').valid).toBe(true);
        expect(E164Phone().validate('+442071234567').valid).toBe(true);
      });

      it('rejects invalid E.164 format', () => {
        expect(E164Phone().validate('15551234567').valid).toBe(false);
        expect(E164Phone().validate('+0123456789').valid).toBe(false);
      });
    });

    describe('UKPhone', () => {
      it('validates UK phone numbers', () => {
        expect(UKPhone().validate('+44 20 7123 4567').valid).toBe(true);
        expect(UKPhone().validate('020 7123 4567').valid).toBe(true);
      });
    });

    describe('TwitterHandle', () => {
      it('validates Twitter handles', () => {
        expect(TwitterHandle().validate('@user').valid).toBe(true);
        expect(TwitterHandle().validate('user').valid).toBe(true);
        expect(TwitterHandle().validate('@user_123').valid).toBe(true);
      });
    });

    describe('InstagramHandle', () => {
      it('validates Instagram handles', () => {
        expect(InstagramHandle().validate('@user').valid).toBe(true);
        expect(InstagramHandle().validate('user.name').valid).toBe(true);
      });
    });

    describe('LinkedInURL', () => {
      it('validates LinkedIn profile URLs', () => {
        expect(LinkedInURL().validate('https://linkedin.com/in/johndoe').valid).toBe(true);
        expect(LinkedInURL().validate('https://www.linkedin.com/in/jane-doe').valid).toBe(true);
      });
    });

    describe('ContactForm', () => {
      it('validates contact forms', () => {
        expect(ContactForm().validate({
          name: 'John Doe',
          email: 'john@example.com',
          message: 'Hello, this is a test message!'
        }).valid).toBe(true);
      });

      it('generates valid contact forms (round-trip)', () => {
        testRoundTrip(ContactForm);
      });
    });

    describe('FullContact', () => {
      it('generates valid full contacts (round-trip)', () => {
        testRoundTrip(FullContact);
      });
    });
  });

  // ============================================================================
  // Credential validators
  // ============================================================================

  describe('Credential validators', () => {
    describe('Username', () => {
      it('validates valid usernames', () => {
        expect(Username().validate('alice').valid).toBe(true);
        expect(Username().validate('user_123').valid).toBe(true);
        expect(Username().validate('johndoe99').valid).toBe(true);
      });

      it('rejects invalid usernames', () => {
        expect(Username().validate('ab').valid).toBe(false);
        expect(Username().validate('123user').valid).toBe(false);
        expect(Username().validate('user-name').valid).toBe(false);
      });
    });

    describe('UsernameWithDots', () => {
      it('validates usernames with dots', () => {
        expect(UsernameWithDots().validate('john.doe').valid).toBe(true);
        expect(UsernameWithDots().validate('user.name.123').valid).toBe(true);
      });
    });

    describe('Handle', () => {
      it('validates handles starting with @', () => {
        expect(Handle().validate('@alice').valid).toBe(true);
        expect(Handle().validate('@user_123').valid).toBe(true);
      });
    });

    describe('Password', () => {
      it('generates valid passwords (round-trip)', () => {
        testRoundTrip(Password);
      });
    });

    describe('PIN', () => {
      it('validates 4 or 6 digit PINs', () => {
        expect(PIN().validate('1234').valid).toBe(true);
        expect(PIN().validate('123456').valid).toBe(true);
      });
    });

    describe('PIN4', () => {
      it('validates 4-digit PINs', () => {
        expect(PIN4().validate('1234').valid).toBe(true);
        expect(PIN4().validate('0000').valid).toBe(true);
      });

      it('rejects invalid PINs', () => {
        expect(PIN4().validate('123').valid).toBe(false);
        expect(PIN4().validate('12345').valid).toBe(false);
        expect(PIN4().validate('abcd').valid).toBe(false);
      });

      it('generates valid PINs (round-trip)', () => {
        testRoundTrip(PIN4);
      });
    });

    describe('PIN6', () => {
      it('validates 6-digit PINs', () => {
        expect(PIN6().validate('123456').valid).toBe(true);
      });

      it('generates valid PINs (round-trip)', () => {
        testRoundTrip(PIN6);
      });
    });

    describe('JWT', () => {
      it('validates JWT format', () => {
        expect(JWT().validate('eyJhbGciOiJIUzI1NiJ9.eyJzdWIiOiIxMjM0NTY3ODkwIn0.dozjgNryP4J3jVmNHl0w5N_XgL0n3I9PlFUP0THsR8U').valid).toBe(true);
      });

      it('rejects invalid JWT format', () => {
        expect(JWT().validate('not.a.jwt.token').valid).toBe(false);
        expect(JWT().validate('invalid').valid).toBe(false);
      });
    });

    describe('APIKey', () => {
      it('generates valid API keys (round-trip)', () => {
        for (let i = 0; i < 5; i++) {
          const generated = generator.generate(APIKey().domain);
          expect(generated.length).toBeGreaterThanOrEqual(32);
          expect(generated.length).toBeLessThanOrEqual(64);
          expect(APIKey().validate(generated).valid).toBe(true);
        }
      });
    });

    describe('BearerToken', () => {
      it('validates Bearer token format', () => {
        expect(BearerToken().validate('Bearer abc123').valid).toBe(true);
        expect(BearerToken().validate('Bearer eyJhbGciOiJIUzI1NiJ9').valid).toBe(true);
      });
    });
  });

  // ============================================================================
  // DateTime validators
  // ============================================================================

  describe('DateTime validators', () => {
    describe('ISODate', () => {
      it('validates ISO dates', () => {
        expect(ISODate().validate('2024-01-15').valid).toBe(true);
        expect(ISODate().validate('2024-12-31').valid).toBe(true);
      });

      it('rejects invalid dates', () => {
        expect(ISODate().validate('2024-13-01').valid).toBe(false);
        expect(ISODate().validate('2024-01-32').valid).toBe(false);
        expect(ISODate().validate('01/15/2024').valid).toBe(false);
      });
    });

    describe('ISODateTime', () => {
      it('validates ISO datetimes', () => {
        expect(ISODateTime().validate('2024-01-15T10:30:00').valid).toBe(true);
        expect(ISODateTime().validate('2024-01-15T10:30:00Z').valid).toBe(true);
        expect(ISODateTime().validate('2024-01-15T10:30:00+05:00').valid).toBe(true);
        expect(ISODateTime().validate('2024-01-15T10:30:00.123Z').valid).toBe(true);
      });

      it('rejects invalid datetimes', () => {
        expect(ISODateTime().validate('2024-01-15').valid).toBe(false);
        expect(ISODateTime().validate('2024-01-15 10:30:00').valid).toBe(false);
      });
    });

    describe('USDate', () => {
      it('validates US date format', () => {
        expect(USDate().validate('01/15/2024').valid).toBe(true);
        expect(USDate().validate('12/31/2024').valid).toBe(true);
      });

      it('rejects invalid US dates', () => {
        expect(USDate().validate('13/01/2024').valid).toBe(false);
      });
    });

    describe('EUDate', () => {
      it('validates EU date format', () => {
        expect(EUDate().validate('15/01/2024').valid).toBe(true);
        expect(EUDate().validate('31/12/2024').valid).toBe(true);
      });
    });

    describe('Year', () => {
      it('validates years', () => {
        expect(Year().validate(2024).valid).toBe(true);
        expect(Year().validate(1000).valid).toBe(true);
        expect(Year().validate(9999).valid).toBe(true);
      });

      it('rejects invalid years', () => {
        expect(Year().validate(999).valid).toBe(false);
      });
    });

    describe('Month', () => {
      it('validates months 1-12', () => {
        expect(Month().validate(1).valid).toBe(true);
        expect(Month().validate(12).valid).toBe(true);
      });

      it('rejects invalid months', () => {
        expect(Month().validate(0).valid).toBe(false);
        expect(Month().validate(13).valid).toBe(false);
      });
    });

    describe('DayOfMonth', () => {
      it('validates days 1-31', () => {
        expect(DayOfMonth().validate(1).valid).toBe(true);
        expect(DayOfMonth().validate(31).valid).toBe(true);
      });
    });

    describe('Time24', () => {
      it('validates 24-hour times', () => {
        expect(Time24().validate('00:00').valid).toBe(true);
        expect(Time24().validate('23:59').valid).toBe(true);
        expect(Time24().validate('12:30').valid).toBe(true);
      });

      it('rejects invalid times', () => {
        expect(Time24().validate('24:00').valid).toBe(false);
        expect(Time24().validate('12:60').valid).toBe(false);
      });
    });

    describe('Time24WithSeconds', () => {
      it('validates 24-hour times with seconds', () => {
        expect(Time24WithSeconds().validate('12:30:45').valid).toBe(true);
        expect(Time24WithSeconds().validate('00:00:00').valid).toBe(true);
      });
    });

    describe('Time12', () => {
      it('validates 12-hour times', () => {
        expect(Time12().validate('12:30 PM').valid).toBe(true);
        expect(Time12().validate('1:30 AM').valid).toBe(true);
        expect(Time12().validate('12:30pm').valid).toBe(true);
      });
    });

    describe('Hour24', () => {
      it('validates hours 0-23', () => {
        expect(Hour24().validate(0).valid).toBe(true);
        expect(Hour24().validate(23).valid).toBe(true);
      });
    });

    describe('Hour12', () => {
      it('validates hours 1-12', () => {
        expect(Hour12().validate(1).valid).toBe(true);
        expect(Hour12().validate(12).valid).toBe(true);
      });
    });

    describe('Minute', () => {
      it('validates minutes 0-59', () => {
        expect(Minute().validate(0).valid).toBe(true);
        expect(Minute().validate(59).valid).toBe(true);
      });
    });

    describe('Second', () => {
      it('validates seconds 0-59', () => {
        expect(Second().validate(0).valid).toBe(true);
        expect(Second().validate(59).valid).toBe(true);
      });
    });

    describe('IANATimezone', () => {
      it('generates valid timezones (round-trip)', () => {
        testRoundTrip(IANATimezone);
      });
    });

    describe('UTCOffset', () => {
      it('generates valid offsets (round-trip)', () => {
        testRoundTrip(UTCOffset);
      });
    });

    describe('ISODuration', () => {
      it('validates ISO 8601 durations', () => {
        expect(ISODuration().validate('P1Y').valid).toBe(true);
        expect(ISODuration().validate('P1Y2M3D').valid).toBe(true);
        expect(ISODuration().validate('PT1H2M3S').valid).toBe(true);
        expect(ISODuration().validate('P1Y2M3DT4H5M6S').valid).toBe(true);
      });
    });

    describe('DurationMs', () => {
      it('validates milliseconds', () => {
        expect(DurationMs().validate(0).valid).toBe(true);
        expect(DurationMs().validate(1000).valid).toBe(true);
      });
    });

    describe('DurationSeconds', () => {
      it('validates seconds', () => {
        expect(DurationSeconds().validate(0).valid).toBe(true);
        expect(DurationSeconds().validate(3600).valid).toBe(true);
      });
    });

    describe('DateRange', () => {
      it('validates date ranges', () => {
        expect(DateRange().validate({ 
          start: '2024-01-01', 
          end: '2024-12-31' 
        }).valid).toBe(true);
      });

      it('generates valid ranges (round-trip)', () => {
        testRoundTrip(DateRange);
      });
    });

    describe('DateTimeRange', () => {
      it('validates datetime ranges', () => {
        expect(DateTimeRange().validate({ 
          start: '2024-01-01T00:00:00Z', 
          end: '2024-12-31T23:59:59Z' 
        }).valid).toBe(true);
      });
    });

    describe('ScheduledEvent', () => {
      it('generates valid events (round-trip)', () => {
        testRoundTrip(ScheduledEvent);
      });
    });

    describe('CronExpression', () => {
      it('validates cron expressions', () => {
        expect(CronExpression().validate('0 0 * * *').valid).toBe(true);
        expect(CronExpression().validate('30 4 1 * 5').valid).toBe(true);
        expect(CronExpression().validate('* * * * *').valid).toBe(true);
      });
    });
  });

  // ============================================================================
  // Financial validators
  // ============================================================================

  describe('Financial validators', () => {
    describe('CreditCardNumber', () => {
      it('validates credit card formats', () => {
        expect(CreditCardNumber().validate('4111111111111111').valid).toBe(true);
        expect(CreditCardNumber().validate('4111 1111 1111 1111').valid).toBe(true);
        expect(CreditCardNumber().validate('4111-1111-1111-1111').valid).toBe(true);
      });
    });

    describe('VisaCard', () => {
      it('validates Visa cards', () => {
        expect(VisaCard().validate('4111111111111111').valid).toBe(true);
        expect(VisaCard().validate('4111111111111').valid).toBe(true);
      });
    });

    describe('MasterCard', () => {
      it('validates Mastercard', () => {
        expect(MasterCard().validate('5111111111111118').valid).toBe(true);
      });
    });

    describe('AmexCard', () => {
      it('validates American Express', () => {
        expect(AmexCard().validate('341111111111111').valid).toBe(true);
        expect(AmexCard().validate('371111111111114').valid).toBe(true);
      });
    });

    describe('CVV', () => {
      it('validates CVV codes (round-trip)', () => {
        for (let i = 0; i < 5; i++) {
          const generated = generator.generate(CVV().domain);
          expect(generated).toMatch(/^\d{3,4}$/);
          expect(CVV().validate(generated).valid).toBe(true);
        }
      });
    });

    describe('CardExpiryShort', () => {
      it('validates MM/YY format', () => {
        expect(CardExpiryShort().validate('12/25').valid).toBe(true);
        expect(CardExpiryShort().validate('01/30').valid).toBe(true);
      });
    });

    describe('CardExpiryLong', () => {
      it('validates MM/YYYY format', () => {
        expect(CardExpiryLong().validate('12/2025').valid).toBe(true);
      });
    });

    describe('CardExpiry', () => {
      it('validates either expiry format', () => {
        expect(CardExpiry().validate('12/25').valid).toBe(true);
        expect(CardExpiry().validate('12/2025').valid).toBe(true);
      });
    });

    describe('CreditCard', () => {
      it('validates full credit card struct', () => {
        expect(CreditCard().validate({
          number: '4111111111111111',
          expiry: '12/25',
          cvv: '123',
          name: 'John Doe'
        }).valid).toBe(true);
      });

      it('generates valid cards (round-trip)', () => {
        testRoundTrip(CreditCard);
      });
    });

    describe('CurrencyCode', () => {
      it('validates 3-letter currency codes (round-trip)', () => {
        for (let i = 0; i < 5; i++) {
          const generated = generator.generate(CurrencyCode().domain);
          expect(generated).toMatch(/^[A-Z]{3}$/);
          expect(CurrencyCode().validate(generated).valid).toBe(true);
        }
      });
    });

    describe('MoneyAmount', () => {
      it('validates money amounts', () => {
        expect(MoneyAmount().validate('100').valid).toBe(true);
        expect(MoneyAmount().validate('100.00').valid).toBe(true);
        expect(MoneyAmount().validate('0.99').valid).toBe(true);
      });
    });

    describe('Price', () => {
      it('validates prices including negative', () => {
        expect(Price().validate('100.00').valid).toBe(true);
        expect(Price().validate('-50.00').valid).toBe(true);
      });
    });

    describe('Percentage', () => {
      it('validates percentages 0-100', () => {
        expect(Percentage().validate(0).valid).toBe(true);
        expect(Percentage().validate(50.5).valid).toBe(true);
        expect(Percentage().validate(100).valid).toBe(true);
      });
    });

    describe('Money', () => {
      it('validates money struct', () => {
        expect(Money().validate({ amount: 100.50, currency: 'USD' }).valid).toBe(true);
      });

      it('generates valid money (round-trip)', () => {
        testRoundTrip(Money);
      });
    });

    describe('USRoutingNumber', () => {
      it('generates valid 9-digit routing numbers (round-trip)', () => {
        testRoundTrip(USRoutingNumber);
      });
    });

    describe('USBankAccountNumber', () => {
      it('generates valid account numbers (round-trip)', () => {
        testRoundTrip(USBankAccountNumber);
      });
    });

    describe('IBAN', () => {
      it('generates valid IBANs (round-trip)', () => {
        testRoundTrip(IBAN);
      });
    });

    describe('SWIFT', () => {
      it('validates SWIFT codes', () => {
        expect(SWIFT().validate('DEUTDEFF').valid).toBe(true);
        expect(SWIFT().validate('DEUTDEFFXXX').valid).toBe(true);
      });
    });

    describe('USBankAccount', () => {
      it('validates bank account struct', () => {
        expect(USBankAccount().validate({
          routingNumber: '123456789',
          accountNumber: '12345678901234',
          accountType: 'checking'
        }).valid).toBe(true);
      });

      it('generates valid accounts (round-trip)', () => {
        testRoundTrip(USBankAccount);
      });
    });

    describe('SSNFormatted', () => {
      it('generates valid formatted SSNs (round-trip)', () => {
        testRoundTrip(SSNFormatted);
      });
    });

    describe('SSN', () => {
      it('validates SSN formats', () => {
        expect(SSN().validate('123-45-6789').valid).toBe(true);
        expect(SSN().validate('123456789').valid).toBe(true);
      });
    });

    describe('EINFormatted', () => {
      it('generates valid formatted EINs (round-trip)', () => {
        testRoundTrip(EINFormatted);
      });
    });

    describe('EIN', () => {
      it('validates EIN formats', () => {
        expect(EIN().validate('12-3456789').valid).toBe(true);
        expect(EIN().validate('123456789').valid).toBe(true);
      });
    });

    describe('UKVAT', () => {
      it('generates valid UK VAT numbers (round-trip)', () => {
        testRoundTrip(UKVAT);
      });
    });

    describe('EUVAT', () => {
      it('generates valid EU VAT numbers (round-trip)', () => {
        testRoundTrip(EUVAT);
      });
    });

    describe('Transaction', () => {
      it('generates valid transactions (round-trip)', () => {
        testRoundTrip(Transaction);
      });
    });

    describe('PaymentMethod', () => {
      it('validates payment methods', () => {
        expect(PaymentMethod().validate({ type: 'card', last4: '1234' }).valid).toBe(true);
        expect(PaymentMethod().validate({ type: 'bank', last4: '5678' }).valid).toBe(true);
      });

      it('generates valid methods (round-trip)', () => {
        testRoundTrip(PaymentMethod);
      });
    });
  });

  // ============================================================================
  // Location validators
  // ============================================================================

  describe('Location validators', () => {
    describe('USZip5', () => {
      it('generates valid 5-digit ZIP (round-trip)', () => {
        testRoundTrip(USZip5);
      });
    });

    describe('USZipPlus4', () => {
      it('generates valid ZIP+4 (round-trip)', () => {
        testRoundTrip(USZipPlus4);
      });
    });

    describe('USZipCode', () => {
      it('validates US ZIP codes', () => {
        expect(USZipCode().validate('12345').valid).toBe(true);
        expect(USZipCode().validate('12345-6789').valid).toBe(true);
      });

      it('rejects invalid ZIP codes', () => {
        expect(USZipCode().validate('1234').valid).toBe(false);
        expect(USZipCode().validate('123456').valid).toBe(false);
      });
    });

    describe('UKPostcode', () => {
      it('validates UK postcodes', () => {
        expect(UKPostcode().validate('SW1A 1AA').valid).toBe(true);
        expect(UKPostcode().validate('EC1A 1BB').valid).toBe(true);
        expect(UKPostcode().validate('M1 1AE').valid).toBe(true);
      });
    });

    describe('CanadianPostalCode', () => {
      it('validates Canadian postal codes', () => {
        expect(CanadianPostalCode().validate('K1A 0B1').valid).toBe(true);
        expect(CanadianPostalCode().validate('M5V3L9').valid).toBe(true);
      });
    });

    describe('GermanPLZ', () => {
      it('generates valid German PLZ (round-trip)', () => {
        testRoundTrip(GermanPLZ);
      });
    });

    describe('PostalCode', () => {
      it('generates valid postal codes (round-trip)', () => {
        testRoundTrip(PostalCode);
      });
    });

    describe('Latitude', () => {
      it('validates latitudes', () => {
        expect(Latitude().validate(0).valid).toBe(true);
        expect(Latitude().validate(45.5).valid).toBe(true);
        expect(Latitude().validate(-90).valid).toBe(true);
        expect(Latitude().validate(90).valid).toBe(true);
      });

      it('rejects invalid latitudes', () => {
        expect(Latitude().validate(-91).valid).toBe(false);
        expect(Latitude().validate(91).valid).toBe(false);
      });
    });

    describe('Longitude', () => {
      it('validates longitudes', () => {
        expect(Longitude().validate(0).valid).toBe(true);
        expect(Longitude().validate(-180).valid).toBe(true);
        expect(Longitude().validate(180).valid).toBe(true);
      });

      it('rejects invalid longitudes', () => {
        expect(Longitude().validate(-181).valid).toBe(false);
        expect(Longitude().validate(181).valid).toBe(false);
      });
    });

    describe('Coordinates', () => {
      it('validates coordinate pairs', () => {
        expect(Coordinates().validate({ latitude: 40.7128, longitude: -74.0060 }).valid).toBe(true);
      });

      it('generates valid coordinates (round-trip)', () => {
        testRoundTrip(Coordinates);
      });
    });

    describe('Coordinates3D', () => {
      it('validates 3D coordinates', () => {
        expect(Coordinates3D().validate({ 
          latitude: 40.7128, 
          longitude: -74.0060, 
          altitude: 10 
        }).valid).toBe(true);
      });

      it('generates valid 3D coordinates (round-trip)', () => {
        testRoundTrip(Coordinates3D);
      });
    });

    describe('CountryCodeAlpha2', () => {
      it('generates valid 2-letter codes (round-trip)', () => {
        for (let i = 0; i < 5; i++) {
          const generated = generator.generate(CountryCodeAlpha2().domain);
          expect(generated).toMatch(/^[A-Z]{2}$/);
          expect(CountryCodeAlpha2().validate(generated).valid).toBe(true);
        }
      });
    });

    describe('CountryCodeAlpha3', () => {
      it('generates valid 3-letter codes (round-trip)', () => {
        for (let i = 0; i < 5; i++) {
          const generated = generator.generate(CountryCodeAlpha3().domain);
          expect(generated).toMatch(/^[A-Z]{3}$/);
        }
      });
    });

    describe('USStateCode', () => {
      it('validates US state codes', () => {
        expect(USStateCode().validate('CA').valid).toBe(true);
        expect(USStateCode().validate('NY').valid).toBe(true);
        expect(USStateCode().validate('TX').valid).toBe(true);
      });

      it('rejects invalid state codes', () => {
        expect(USStateCode().validate('XX').valid).toBe(false);
      });
    });

    describe('USAddress', () => {
      it('generates valid US addresses (round-trip)', () => {
        testRoundTrip(USAddress);
      });
    });

    describe('UKAddress', () => {
      it('generates valid UK addresses (round-trip)', () => {
        testRoundTrip(UKAddress);
      });
    });

    describe('InternationalAddress', () => {
      it('generates valid international addresses (round-trip)', () => {
        testRoundTrip(InternationalAddress);
      });
    });

    describe('ShippingAddress', () => {
      it('generates valid shipping addresses (round-trip)', () => {
        testRoundTrip(ShippingAddress);
      });
    });

    describe('GeoLocation', () => {
      it('generates valid geolocations (round-trip)', () => {
        testRoundTrip(GeoLocation);
      });
    });
  });

  // ============================================================================
  // Preset validators (realistic generation)
  // ============================================================================

  describe('Preset validators', () => {
    describe('FirstName', () => {
      it('generates realistic first names', () => {
        for (let i = 0; i < 10; i++) {
          const generated = generator.generate(FirstName().domain);
          expect(generated).toBeTruthy();
          expect(typeof generated).toBe('string');
          expect(generated.length).toBeGreaterThan(0);
        }
      });
    });

    describe('LastName', () => {
      it('generates realistic last names', () => {
        for (let i = 0; i < 10; i++) {
          const generated = generator.generate(LastName().domain);
          expect(generated).toBeTruthy();
          expect(typeof generated).toBe('string');
        }
      });
    });

    describe('FullName', () => {
      it('generates realistic full names', () => {
        for (let i = 0; i < 10; i++) {
          const generated = generator.generate(FullName().domain);
          expect(generated).toContain(' ');
        }
      });
    });

    describe('RealisticUsername', () => {
      it('generates usernames that validate', () => {
        for (let i = 0; i < 10; i++) {
          const generated = generator.generate(RealisticUsername().domain);
          expect(Username().validate(generated).valid).toBe(true);
        }
      });
    });

    describe('RealisticEmail', () => {
      it('generates realistic emails that validate (all styles)', () => {
        // Run many iterations to hit all 4 switch branches
        for (let i = 0; i < 100; i++) {
          const generated = generator.generate(RealisticEmail().domain);
          expect(Email().validate(generated).valid).toBe(true);
        }
      });
    });

    describe('CorporateEmailPreset', () => {
      it('generates corporate emails', () => {
        for (let i = 0; i < 10; i++) {
          const generated = generator.generate(CorporateEmailPreset().domain);
          expect(Email().validate(generated).valid).toBe(true);
        }
      });
    });

    describe('RealisticStreetAddress', () => {
      it('generates street addresses', () => {
        for (let i = 0; i < 10; i++) {
          const generated = generator.generate(RealisticStreetAddress().domain);
          expect(generated.length).toBeGreaterThan(0);
        }
      });
    });

    describe('RealisticCity', () => {
      it('generates city names', () => {
        for (let i = 0; i < 10; i++) {
          const generated = generator.generate(RealisticCity().domain);
          expect(generated.length).toBeGreaterThan(0);
        }
      });
    });

    describe('RealisticState', () => {
      it('generates US state codes', () => {
        for (let i = 0; i < 10; i++) {
          const generated = generator.generate(RealisticState().domain);
          expect(generated).toMatch(/^[A-Z]{2}$/);
        }
      });
    });

    describe('RealisticZipCode', () => {
      it('generates ZIP codes that validate (both formats)', () => {
        // Run many iterations to hit both branches (ZIP5 and ZIP+4)
        for (let i = 0; i < 50; i++) {
          const generated = generator.generate(RealisticZipCode().domain);
          expect(USZipCode().validate(generated).valid).toBe(true);
        }
      });
    });

    describe('RealisticUSPhone', () => {
      it('generates US phones that validate (all formats)', () => {
        // Run many iterations to hit all phone format branches
        for (let i = 0; i < 50; i++) {
          const generated = generator.generate(RealisticUSPhone().domain);
          expect(USPhone().validate(generated).valid).toBe(true);
        }
      });
    });

    describe('CompanyName', () => {
      it('generates company names', () => {
        for (let i = 0; i < 10; i++) {
          const generated = generator.generate(CompanyName().domain);
          expect(generated.length).toBeGreaterThan(0);
        }
      });
    });

    describe('ProductName', () => {
      it('generates product names', () => {
        for (let i = 0; i < 10; i++) {
          const generated = generator.generate(ProductName().domain);
          expect(generated.length).toBeGreaterThan(0);
        }
      });
    });

    describe('LoremIpsum', () => {
      it('generates lorem ipsum text with custom params', () => {
        for (let i = 0; i < 5; i++) {
          const generated = generator.generate(LoremIpsum(5, 20).domain);
          expect(generated.length).toBeGreaterThan(0);
          expect(generated.endsWith('.')).toBe(true);
        }
      });

      it('generates lorem ipsum text with default params', () => {
        for (let i = 0; i < 5; i++) {
          const generated = generator.generate(LoremIpsum().domain);
          expect(generated.length).toBeGreaterThan(0);
          expect(generated.endsWith('.')).toBe(true);
        }
      });
    });

    describe('RecentDate', () => {
      it('generates recent ISO dates', () => {
        for (let i = 0; i < 10; i++) {
          const generated = generator.generate(RecentDate().domain);
          expect(generated).toMatch(/^\d{4}-\d{2}-\d{2}$/);
        }
      });
    });

    describe('FutureDate', () => {
      it('generates future ISO dates', () => {
        for (let i = 0; i < 10; i++) {
          const generated = generator.generate(FutureDate().domain);
          expect(generated).toMatch(/^\d{4}-\d{2}-\d{2}$/);
        }
      });
    });

    describe('RealisticPrice', () => {
      it('generates realistic prices', () => {
        for (let i = 0; i < 10; i++) {
          const generated = generator.generate(RealisticPrice().domain);
          expect(typeof generated).toBe('number');
          expect(generated).toBeGreaterThanOrEqual(0);
        }
      });
    });
  });
});
