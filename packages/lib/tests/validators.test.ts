/**
 * Tests for @janus-validator/lib validators
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
  IPv4,
  IPv6,
  Port,
  MACAddress,
  Domain,
  
  // Identifiers
  UUID,
  UUIDv4,
  Slug,
  NanoID,
  SemVer,
  HexColor6,
  
  // Contact
  Email,
  USPhone,
  E164Phone,
  
  // Credentials
  Username,
  Password,
  PIN4,
  JWT,
  
  // DateTime
  ISODate,
  ISODateTime,
  Time24,
  
  // Financial
  CurrencyCode,
  IBAN,
  CVV,
  
  // Location
  USZipCode,
  Latitude,
  Longitude,
  CountryCodeAlpha2,
  
  // Presets
  FirstName,
  LastName,
  RealisticEmail,
} from '../src';

describe('@janus-validator/lib', () => {
  const generator = new Generator({ random: Math.random });

  // ============================================================================
  // Network validators
  // ============================================================================

  describe('Network validators', () => {
    describe('URL', () => {
      it('validates valid URLs', () => {
        expect(URL().validate('http://example.com').valid).toBe(true);
        expect(URL().validate('https://example.com/path').valid).toBe(true);
        expect(URL().validate('https://example.com:8080/path?query=1').valid).toBe(true);
      });

      it('rejects invalid URLs', () => {
        expect(URL().validate('not-a-url').valid).toBe(false);
        expect(URL().validate('ftp://example.com').valid).toBe(false);
      });
    });

    describe('IPv4', () => {
      it('validates valid IPv4 addresses', () => {
        expect(IPv4().validate('192.168.1.1').valid).toBe(true);
        expect(IPv4().validate('0.0.0.0').valid).toBe(true);
        expect(IPv4().validate('255.255.255.255').valid).toBe(true);
      });

      it('rejects invalid IPv4 addresses', () => {
        expect(IPv4().validate('256.0.0.0').valid).toBe(false);
        expect(IPv4().validate('192.168.1').valid).toBe(false);
        expect(IPv4().validate('abc.def.ghi.jkl').valid).toBe(false);
      });
    });

    describe('Port', () => {
      it('validates valid ports', () => {
        expect(Port().validate(80).valid).toBe(true);
        expect(Port().validate(443).valid).toBe(true);
        expect(Port().validate(65535).valid).toBe(true);
      });

      it('rejects invalid ports', () => {
        expect(Port().validate(0).valid).toBe(false);
        expect(Port().validate(65536).valid).toBe(false);
        expect(Port().validate(-1).valid).toBe(false);
      });
    });

    describe('Domain', () => {
      it('validates valid domain names', () => {
        expect(Domain().validate('example.com').valid).toBe(true);
        expect(Domain().validate('sub.example.com').valid).toBe(true);
        expect(Domain().validate('deep.sub.example.co.uk').valid).toBe(true);
      });

      it('rejects invalid domain names', () => {
        expect(Domain().validate('example').valid).toBe(false);
        expect(Domain().validate('-example.com').valid).toBe(false);
      });
    });
  });

  // ============================================================================
  // Identifier validators
  // ============================================================================

  describe('Identifier validators', () => {
    describe('UUIDv4', () => {
      it('validates valid UUIDv4', () => {
        expect(UUIDv4().validate('550e8400-e29b-41d4-a716-446655440000').valid).toBe(true);
        expect(UUIDv4().validate('550E8400-E29B-41D4-A716-446655440000').valid).toBe(true);
      });

      it('rejects invalid UUIDs', () => {
        expect(UUIDv4().validate('not-a-uuid').valid).toBe(false);
        expect(UUIDv4().validate('550e8400-e29b-21d4-a716-446655440000').valid).toBe(false); // Wrong version
      });

      it('generates valid UUIDs (round-trip)', () => {
        for (let i = 0; i < 10; i++) {
          const generated = generator.generate(UUIDv4().domain);
          const result = UUIDv4().validate(generated);
          expect(result.valid).toBe(true);
        }
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

    describe('SemVer', () => {
      it('validates semantic versions', () => {
        expect(SemVer().validate('1.0.0').valid).toBe(true);
        expect(SemVer().validate('12.34.56').valid).toBe(true);
      });

      it('generates valid versions (round-trip)', () => {
        for (let i = 0; i < 10; i++) {
          const generated = generator.generate(SemVer().domain);
          const result = SemVer().validate(generated);
          expect(result.valid).toBe(true);
        }
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

      it('generates valid emails (round-trip)', () => {
        for (let i = 0; i < 10; i++) {
          const generated = generator.generate(Email().domain);
          const result = Email().validate(generated);
          expect(result.valid).toBe(true);
        }
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

    describe('Password', () => {
      it('generates valid passwords (round-trip)', () => {
        for (let i = 0; i < 10; i++) {
          const generated = generator.generate(Password().domain);
          const result = Password().validate(generated);
          expect(result.valid).toBe(true);
        }
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
      });

      it('rejects invalid datetimes', () => {
        expect(ISODateTime().validate('2024-01-15').valid).toBe(false);
        expect(ISODateTime().validate('2024-01-15 10:30:00').valid).toBe(false);
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
  });

  // ============================================================================
  // Financial validators
  // ============================================================================

  describe('Financial validators', () => {
    describe('CurrencyCode', () => {
      it('validates currency codes (generation round-trip)', () => {
        for (let i = 0; i < 10; i++) {
          const generated = generator.generate(CurrencyCode().domain);
          const result = CurrencyCode().validate(generated);
          expect(result.valid).toBe(true);
          expect(generated).toMatch(/^[A-Z]{3}$/);
        }
      });
    });

    describe('CVV', () => {
      it('validates CVV codes (generation round-trip)', () => {
        for (let i = 0; i < 10; i++) {
          const generated = generator.generate(CVV().domain);
          const result = CVV().validate(generated);
          expect(result.valid).toBe(true);
          expect(generated).toMatch(/^\d{3,4}$/);
        }
      });
    });
  });

  // ============================================================================
  // Location validators
  // ============================================================================

  describe('Location validators', () => {
    describe('USZipCode', () => {
      it('validates US ZIP codes', () => {
        expect(USZipCode().validate('12345').valid).toBe(true);
        expect(USZipCode().validate('12345-6789').valid).toBe(true);
      });

      it('rejects invalid ZIP codes', () => {
        expect(USZipCode().validate('1234').valid).toBe(false);
        expect(USZipCode().validate('123456').valid).toBe(false);
      });

      it('generates valid ZIP codes (round-trip)', () => {
        for (let i = 0; i < 10; i++) {
          const generated = generator.generate(USZipCode().domain);
          const result = USZipCode().validate(generated);
          expect(result.valid).toBe(true);
        }
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

    describe('CountryCodeAlpha2', () => {
      it('generates valid country codes (round-trip)', () => {
        for (let i = 0; i < 10; i++) {
          const generated = generator.generate(CountryCodeAlpha2().domain);
          const result = CountryCodeAlpha2().validate(generated);
          expect(result.valid).toBe(true);
          expect(generated).toMatch(/^[A-Z]{2}$/);
        }
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
          expect(generated.length).toBeGreaterThan(0);
        }
      });
    });

    describe('RealisticEmail', () => {
      it('generates realistic emails that validate', () => {
        for (let i = 0; i < 10; i++) {
          const generated = generator.generate(RealisticEmail().domain);
          const result = Email().validate(generated);
          expect(result.valid).toBe(true);
        }
      });
    });
  });
});
