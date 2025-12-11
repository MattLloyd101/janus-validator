/**
 * Tests for the common validation patterns library
 */

import {
  // Credentials
  Username, Handle, Password, StrongPassword, PIN,
  PasswordWithConfirmation, JWT,
  // Contact
  Email, USPhone, E164Phone,
  TwitterHandle, ContactForm,
  // Network
  URL, SecureURL, Domain, IPv4, Port, MACAddress,
  // Location
  USZipCode, UKPostcode, Coordinates,
  CountryCodeAlpha2, USStateCode,
  // Finance
  CreditCardNumber, VisaCard, CVV, CardExpiry, CurrencyCode, SSN, IBAN, SWIFT,
  // DateTime
  ISODate, ISODateTime, USDate, Time24, Year, Month,
  // Identifiers
  UUIDv4, Slug, IntegerID, ObjectID, SemVer, HexColor, MD5Hash,
} from '@/com/techlloyd/janus/lib';

describe('Lib - Common Validation Patterns', () => {
  describe('Credentials', () => {
    it('Username should validate alphanumeric usernames', () => {
      expect(Username().validate('john_doe').valid).toBe(true);
      expect(Username().validate('Alice123').valid).toBe(true);
      expect(Username().validate('ab').valid).toBe(false); // too short
      expect(Username().validate('123start').valid).toBe(false); // starts with number
    });

    it('Handle should validate @mentions', () => {
      expect(Handle().validate('@john').valid).toBe(true);
      expect(Handle().validate('@alice_123').valid).toBe(true);
    });

    it('Password should validate length', () => {
      expect(Password().validate('short').valid).toBe(false);
      expect(Password().validate('longenough123').valid).toBe(true);
    });

    it('StrongPassword should require complexity', () => {
      expect(StrongPassword().validate('weakpassword').valid).toBe(false);
      // Pattern: [A-Z][a-z]{2,6}[0-9]{2,4}[!@#$%^&*]{1,2}...
      expect(StrongPassword().validate('Abc12!@xyz').valid).toBe(true);
    });

    it('PIN should validate 4 or 6 digits', () => {
      expect(PIN().validate('1234').valid).toBe(true);
      expect(PIN().validate('123456').valid).toBe(true);
      expect(PIN().validate('12345').valid).toBe(false);
    });

    it('PasswordWithConfirmation should validate matching passwords', () => {
      const { validator, context } = PasswordWithConfirmation(8);
      
      expect(validator.validate({
        password: 'secret123',
        confirmPassword: 'secret123',
      }).valid).toBe(true);

      context.clear();

      expect(validator.validate({
        password: 'secret123',
        confirmPassword: 'different',
      }).valid).toBe(false);
    });

    it('JWT should validate token format', () => {
      expect(JWT().validate('eyJhbGciOiJIUzI1NiJ9.eyJzdWIiOiIxMjM0NTY3ODkwIn0.abc123').valid).toBe(true);
      expect(JWT().validate('not.a.jwt.token').valid).toBe(false);
    });
  });

  describe('Contact', () => {
    it('Email should validate email format', () => {
      expect(Email().validate('user@example.com').valid).toBe(true);
      expect(Email().validate('user.name+tag@domain.co.uk').valid).toBe(true);
      expect(Email().validate('invalid-email').valid).toBe(false);
    });

    it('USPhone should validate US phone numbers', () => {
      expect(USPhone().validate('(555) 123-4567').valid).toBe(true);
      expect(USPhone().validate('555-123-4567').valid).toBe(true);
      expect(USPhone().validate('5551234567').valid).toBe(true);
    });

    it('E164Phone should validate international format', () => {
      expect(E164Phone().validate('+14155551234').valid).toBe(true);
      expect(E164Phone().validate('+442071234567').valid).toBe(true);
      expect(E164Phone().validate('14155551234').valid).toBe(false); // missing +
    });

    it('TwitterHandle should validate handles', () => {
      expect(TwitterHandle().validate('elonmusk').valid).toBe(true);
      expect(TwitterHandle().validate('@elonmusk').valid).toBe(true);
    });

    it('ContactForm should validate form data', () => {
      expect(ContactForm().validate({
        name: 'John Doe',
        email: 'john@example.com',
        message: 'Hello, this is a test message.',
      }).valid).toBe(true);
    });
  });

  describe('Network', () => {
    it('URL should validate URLs', () => {
      expect(URL().validate('https://example.com').valid).toBe(true);
      expect(URL().validate('http://sub.domain.com/path?query=1').valid).toBe(true);
      expect(URL().validate('not-a-url').valid).toBe(false);
    });

    it('SecureURL should only accept HTTPS', () => {
      expect(SecureURL().validate('https://example.com').valid).toBe(true);
      expect(SecureURL().validate('http://example.com').valid).toBe(false);
    });

    it('Domain should validate domain names', () => {
      expect(Domain().validate('example.com').valid).toBe(true);
      expect(Domain().validate('sub.domain.co.uk').valid).toBe(true);
    });

    it('IPv4 should validate IPv4 addresses', () => {
      expect(IPv4().validate('192.168.1.1').valid).toBe(true);
      expect(IPv4().validate('255.255.255.255').valid).toBe(true);
      expect(IPv4().validate('256.1.1.1').valid).toBe(false);
      expect(IPv4().validate('1.2.3').valid).toBe(false);
    });

    it('Port should validate port numbers', () => {
      expect(Port().validate(80).valid).toBe(true);
      expect(Port().validate(443).valid).toBe(true);
      expect(Port().validate(65535).valid).toBe(true);
      expect(Port().validate(0).valid).toBe(false);
      expect(Port().validate(70000).valid).toBe(false);
    });

    it('MACAddress should validate MAC addresses', () => {
      expect(MACAddress().validate('00:1A:2B:3C:4D:5E').valid).toBe(true);
      expect(MACAddress().validate('00-1A-2B-3C-4D-5E').valid).toBe(true);
    });
  });

  describe('Location', () => {
    it('USZipCode should validate ZIP codes', () => {
      expect(USZipCode().validate('12345').valid).toBe(true);
      expect(USZipCode().validate('12345-6789').valid).toBe(true);
      expect(USZipCode().validate('1234').valid).toBe(false);
    });

    it('UKPostcode should validate UK postcodes', () => {
      expect(UKPostcode().validate('SW1A 1AA').valid).toBe(true);
      expect(UKPostcode().validate('EC1A1BB').valid).toBe(true);
    });

    it('Coordinates should validate lat/long', () => {
      expect(Coordinates().validate({ latitude: 40.7128, longitude: -74.0060 }).valid).toBe(true);
      expect(Coordinates().validate({ latitude: 91, longitude: 0 }).valid).toBe(false);
      expect(Coordinates().validate({ latitude: 0, longitude: 181 }).valid).toBe(false);
    });

    it('CountryCodeAlpha2 should validate country codes', () => {
      expect(CountryCodeAlpha2().validate('US').valid).toBe(true);
      expect(CountryCodeAlpha2().validate('GB').valid).toBe(true);
      expect(CountryCodeAlpha2().validate('USA').valid).toBe(false);
    });

    it('USStateCode should validate state codes', () => {
      expect(USStateCode().validate('CA').valid).toBe(true);
      expect(USStateCode().validate('NY').valid).toBe(true);
      expect(USStateCode().validate('XX').valid).toBe(false);
    });
  });

  describe('Finance', () => {
    it('CreditCardNumber should validate card format', () => {
      expect(CreditCardNumber().validate('4111111111111111').valid).toBe(true);
      expect(CreditCardNumber().validate('4111 1111 1111 1111').valid).toBe(true);
    });

    it('VisaCard should validate Visa cards', () => {
      expect(VisaCard().validate('4111111111111111').valid).toBe(true);
      expect(VisaCard().validate('5111111111111111').valid).toBe(false);
    });

    it('CVV should validate security codes', () => {
      expect(CVV().validate('123').valid).toBe(true);
      expect(CVV().validate('1234').valid).toBe(true);
      expect(CVV().validate('12').valid).toBe(false);
    });

    it('CardExpiry should validate expiry dates', () => {
      expect(CardExpiry().validate('12/25').valid).toBe(true);
      expect(CardExpiry().validate('01/2030').valid).toBe(true);
      expect(CardExpiry().validate('13/25').valid).toBe(false);
    });

    it('CurrencyCode should validate currency codes', () => {
      expect(CurrencyCode().validate('USD').valid).toBe(true);
      expect(CurrencyCode().validate('EUR').valid).toBe(true);
      expect(CurrencyCode().validate('US').valid).toBe(false);
    });

    it('SSN should validate social security numbers', () => {
      expect(SSN().validate('123-45-6789').valid).toBe(true);
      expect(SSN().validate('123456789').valid).toBe(true);
    });

    it('IBAN should validate IBANs', () => {
      expect(IBAN().validate('DE89370400440532013000').valid).toBe(true);
      expect(IBAN().validate('GB82WEST12345698765432').valid).toBe(true);
    });

    it('SWIFT should validate SWIFT codes', () => {
      expect(SWIFT().validate('DEUTDEFF').valid).toBe(true);
      expect(SWIFT().validate('DEUTDEFF500').valid).toBe(true);
    });
  });

  describe('DateTime', () => {
    it('ISODate should validate ISO dates', () => {
      expect(ISODate().validate('2024-01-15').valid).toBe(true);
      expect(ISODate().validate('2024-13-01').valid).toBe(false);
    });

    it('ISODateTime should validate ISO datetimes', () => {
      expect(ISODateTime().validate('2024-01-15T10:30:00Z').valid).toBe(true);
      expect(ISODateTime().validate('2024-01-15T10:30:00+05:30').valid).toBe(true);
    });

    it('USDate should validate US dates', () => {
      expect(USDate().validate('01/15/2024').valid).toBe(true);
      expect(USDate().validate('13/01/2024').valid).toBe(false);
    });

    it('Time24 should validate 24-hour time', () => {
      expect(Time24().validate('14:30').valid).toBe(true);
      expect(Time24().validate('23:59').valid).toBe(true);
      expect(Time24().validate('24:00').valid).toBe(false);
    });

    it('Year should validate years', () => {
      expect(Year().validate(2024).valid).toBe(true);
      expect(Year().validate(1900).valid).toBe(true);
      expect(Year().validate(999).valid).toBe(false);
    });

    it('Month should validate months', () => {
      expect(Month().validate(1).valid).toBe(true);
      expect(Month().validate(12).valid).toBe(true);
      expect(Month().validate(0).valid).toBe(false);
      expect(Month().validate(13).valid).toBe(false);
    });
  });

  describe('Identifiers', () => {
    it('UUIDv4 should validate v4 UUIDs', () => {
      expect(UUIDv4().validate('550e8400-e29b-41d4-a716-446655440000').valid).toBe(true);
      expect(UUIDv4().validate('not-a-uuid').valid).toBe(false);
    });

    it('Slug should validate URL slugs', () => {
      expect(Slug().validate('my-blog-post').valid).toBe(true);
      expect(Slug().validate('article123').valid).toBe(true);
      expect(Slug().validate('Invalid Slug').valid).toBe(false);
    });

    it('IntegerID should validate positive integers', () => {
      expect(IntegerID().validate(1).valid).toBe(true);
      expect(IntegerID().validate(12345).valid).toBe(true);
      expect(IntegerID().validate(0).valid).toBe(false);
    });

    it('ObjectID should validate MongoDB ObjectIds', () => {
      expect(ObjectID().validate('507f1f77bcf86cd799439011').valid).toBe(true);
      expect(ObjectID().validate('invalid').valid).toBe(false);
    });

    it('SemVer should validate semantic versions', () => {
      expect(SemVer().validate('1.0.0').valid).toBe(true);
      expect(SemVer().validate('2.10.3').valid).toBe(true);
      expect(SemVer().validate('1.0').valid).toBe(false);
    });

    it('HexColor should validate hex colors', () => {
      expect(HexColor().validate('#fff').valid).toBe(true);
      expect(HexColor().validate('#ffffff').valid).toBe(true);
      expect(HexColor().validate('#AABBCC').valid).toBe(true);
      expect(HexColor().validate('ffffff').valid).toBe(false);
    });

    it('MD5Hash should validate MD5 hashes', () => {
      expect(MD5Hash().validate('d41d8cd98f00b204e9800998ecf8427e').valid).toBe(true);
      expect(MD5Hash().validate('invalid').valid).toBe(false);
    });
  });
});

