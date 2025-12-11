/**
 * Tests for realistic value presets
 */

import {
  // Names
  FirstName,
  LastName,
  FullName,
  // Usernames
  RealisticUsername,
  // Emails
  RealisticEmail,
  CorporateEmailPreset,
  // Addresses
  RealisticStreetAddress,
  RealisticCity,
  RealisticState,
  RealisticZipCode,
  // Phone
  RealisticUSPhone,
  // Companies
  CompanyName,
  ProductName,
  LoremIpsum,
  // Dates
  RecentDate,
  FutureDate,
  // Money
  RealisticPrice,
} from '@/com/techlloyd/janus/lib/presets';

import { Generator } from '@/com/techlloyd/janus/Generator';
import { RNG } from '@/com/techlloyd/janus/RNG';

class DefaultRNG implements RNG {
  random(): number {
    return Math.random();
  }
}

const rng = new DefaultRNG();
const generator = new Generator(rng);

describe('Presets - Names', () => {
  describe('FirstName', () => {
    it('should generate valid first names', () => {
      const validator = FirstName();
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator);
        expect(validator.validate(value).valid).toBe(true);
        expect(value.length).toBeGreaterThan(0);
        expect(value).toMatch(/^[A-Z][a-z]+$/);
      }
    });

    it('should generate variety of names', () => {
      const validator = FirstName();
      const names = new Set<string>();
      for (let i = 0; i < 50; i++) {
        names.add(generator.generate(validator));
      }
      expect(names.size).toBeGreaterThan(5);
    });
  });

  describe('LastName', () => {
    it('should generate valid last names', () => {
      const validator = LastName();
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator);
        expect(validator.validate(value).valid).toBe(true);
        expect(value.length).toBeGreaterThan(0);
      }
    });
  });

  describe('FullName', () => {
    it('should generate first and last name', () => {
      const validator = FullName();
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator);
        expect(validator.validate(value).valid).toBe(true);
        expect(value).toMatch(/^[A-Z][a-z]+ [A-Z][a-z]+$/);
      }
    });
  });
});

describe('Presets - Usernames', () => {
  describe('RealisticUsername', () => {
    it('should generate valid usernames', () => {
      const validator = RealisticUsername();
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator);
        expect(validator.validate(value).valid).toBe(true);
      }
    });

    it('should generate gaming-style usernames', () => {
      const validator = RealisticUsername();
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator);
        // Should be adjective_noun + number pattern
        expect(value).toMatch(/^[a-z]+_[a-z]+\d+$/);
      }
    });
  });
});

describe('Presets - Emails', () => {
  describe('RealisticEmail', () => {
    it('should generate valid email addresses', () => {
      const validator = RealisticEmail();
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator);
        expect(validator.validate(value).valid).toBe(true);
        expect(value).toContain('@');
        expect(value).toMatch(/\.(com|net|org|io)$/);
      }
    });

    it('should generate emails from common providers', () => {
      const validator = RealisticEmail();
      const domains = new Set<string>();
      for (let i = 0; i < 50; i++) {
        const email = generator.generate(validator);
        const domain = email.split('@')[1];
        domains.add(domain);
      }
      // Should have multiple domains
      expect(domains.size).toBeGreaterThan(3);
    });
  });

  describe('CorporateEmailPreset', () => {
    it('should generate corporate email format', () => {
      const validator = CorporateEmailPreset();
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator);
        expect(validator.validate(value).valid).toBe(true);
        // Should follow first.last@company format
        expect(value).toMatch(/^[a-z]+\.[a-z]+@[a-z]+\.(com|io|co|net|org)$/);
      }
    });
  });
});

describe('Presets - Addresses', () => {
  describe('RealisticStreetAddress', () => {
    it('should generate valid street addresses', () => {
      const validator = RealisticStreetAddress();
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator);
        expect(validator.validate(value).valid).toBe(true);
        // Should have number, street name, and type
        expect(value).toMatch(/^\d+ [A-Z][a-z]+ (St|Ave|Blvd|Dr|Ln|Rd|Way|Ct)$/);
      }
    });
  });

  describe('RealisticCity', () => {
    it('should generate US city names', () => {
      const validator = RealisticCity();
      const cities = new Set<string>();
      for (let i = 0; i < 50; i++) {
        const value = generator.generate(validator);
        expect(validator.validate(value).valid).toBe(true);
        cities.add(value);
      }
      expect(cities.size).toBeGreaterThan(5);
    });
  });

  describe('RealisticState', () => {
    it('should generate valid US state codes', () => {
      const validator = RealisticState();
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator);
        expect(validator.validate(value).valid).toBe(true);
        expect(value).toMatch(/^[A-Z]{2}$/);
      }
    });

    it('should generate variety of states', () => {
      const validator = RealisticState();
      const states = new Set<string>();
      for (let i = 0; i < 100; i++) {
        states.add(generator.generate(validator));
      }
      expect(states.size).toBeGreaterThan(10);
    });
  });

  describe('RealisticZipCode', () => {
    it('should generate valid ZIP codes', () => {
      const validator = RealisticZipCode();
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator);
        expect(validator.validate(value).valid).toBe(true);
        expect(value).toMatch(/^\d{5}(-\d{4})?$/);
      }
    });

    it('should sometimes generate ZIP+4 format', () => {
      const validator = RealisticZipCode();
      let hasZipPlus4 = false;
      for (let i = 0; i < 50; i++) {
        const value = generator.generate(validator);
        if (value.includes('-')) {
          hasZipPlus4 = true;
          break;
        }
      }
      expect(hasZipPlus4).toBe(true);
    });
  });
});

describe('Presets - Phone', () => {
  describe('RealisticUSPhone', () => {
    it('should generate valid US phone numbers', () => {
      const validator = RealisticUSPhone();
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator);
        expect(validator.validate(value).valid).toBe(true);
      }
    });

    it('should generate different formats', () => {
      const validator = RealisticUSPhone();
      const formats = new Set<string>();
      for (let i = 0; i < 50; i++) {
        const value = generator.generate(validator);
        if (value.startsWith('(')) {
          formats.add('parentheses');
        } else if (value.includes('-')) {
          formats.add('dashes');
        } else if (value.includes('.')) {
          formats.add('dots');
        }
      }
      expect(formats.size).toBeGreaterThan(1);
    });
  });
});

describe('Presets - Companies', () => {
  describe('CompanyName', () => {
    it('should generate company names with suffix', () => {
      const validator = CompanyName();
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator);
        expect(validator.validate(value).valid).toBe(true);
        // Should have company name and suffix
        expect(value).toMatch(/^[A-Za-z]+ (Inc|Corp|LLC|Ltd|Co|Group|Solutions)$/);
      }
    });
  });

  describe('ProductName', () => {
    it('should generate product names', () => {
      const validator = ProductName();
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator);
        expect(validator.validate(value).valid).toBe(true);
        // Should have adjective and type
        expect(value).toMatch(/^(Premium|Deluxe|Pro|Ultra|Elite|Classic|Essential) (Widget|Gadget|Device|Tool|Kit|System|Package)$/);
      }
    });
  });

  describe('LoremIpsum', () => {
    it('should generate lorem ipsum text', () => {
      const validator = LoremIpsum(10, 30);
      for (let i = 0; i < 10; i++) {
        const value = generator.generate(validator);
        expect(validator.validate(value).valid).toBe(true);
        // Should start with capital and end with period
        expect(value).toMatch(/^[A-Z].+\.$/);
      }
    });

    it('should generate text within word range', () => {
      const minWords = 5;
      const maxWords = 15;
      const validator = LoremIpsum(minWords, maxWords);
      
      for (let i = 0; i < 10; i++) {
        const value = generator.generate(validator);
        const wordCount = value.replace(/\.$/, '').split(' ').length;
        expect(wordCount).toBeGreaterThanOrEqual(minWords);
        expect(wordCount).toBeLessThanOrEqual(maxWords);
      }
    });
  });
});

describe('Presets - Dates', () => {
  describe('RecentDate', () => {
    it('should generate valid ISO dates', () => {
      const validator = RecentDate();
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator);
        expect(validator.validate(value).valid).toBe(true);
        expect(value).toMatch(/^\d{4}-\d{2}-\d{2}$/);
      }
    });

    it('should generate dates in the past', () => {
      const validator = RecentDate();
      const now = new Date();
      
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator);
        const date = new Date(value);
        expect(date.getTime()).toBeLessThanOrEqual(now.getTime());
      }
    });

    it('should generate dates within last 5 years', () => {
      const validator = RecentDate();
      const now = new Date();
      const fiveYearsAgo = new Date(now.getTime() - 5 * 365 * 24 * 60 * 60 * 1000);
      
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator);
        const date = new Date(value);
        expect(date.getTime()).toBeGreaterThanOrEqual(fiveYearsAgo.getTime());
      }
    });
  });

  describe('FutureDate', () => {
    it('should generate valid ISO dates', () => {
      const validator = FutureDate();
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator);
        expect(validator.validate(value).valid).toBe(true);
        expect(value).toMatch(/^\d{4}-\d{2}-\d{2}$/);
      }
    });

    it('should generate dates in the future', () => {
      const validator = FutureDate();
      const now = new Date();
      
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator);
        const date = new Date(value);
        expect(date.getTime()).toBeGreaterThan(now.getTime());
      }
    });
  });
});

describe('Presets - Money', () => {
  describe('RealisticPrice', () => {
    it('should generate valid prices', () => {
      const validator = RealisticPrice();
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator);
        expect(validator.validate(value).valid).toBe(true);
        expect(typeof value).toBe('number');
        expect(value).toBeGreaterThanOrEqual(0);
      }
    });

    it('should generate prices with common price points', () => {
      const validator = RealisticPrice();
      const prices: number[] = [];
      
      for (let i = 0; i < 100; i++) {
        prices.push(generator.generate(validator));
      }

      // Check that we have variety in price ranges
      const under20 = prices.filter(p => p < 20).length;
      const under100 = prices.filter(p => p >= 20 && p < 100).length;
      const over100 = prices.filter(p => p >= 100).length;

      expect(under20).toBeGreaterThan(0);
      expect(under100).toBeGreaterThan(0);
      expect(over100).toBeGreaterThan(0);
    });
  });
});

describe('Presets - Property-based tests', () => {
  const presets = [
    { name: 'FirstName', factory: FirstName },
    { name: 'LastName', factory: LastName },
    { name: 'FullName', factory: FullName },
    { name: 'RealisticUsername', factory: RealisticUsername },
    { name: 'RealisticEmail', factory: RealisticEmail },
    { name: 'CorporateEmailPreset', factory: CorporateEmailPreset },
    { name: 'RealisticStreetAddress', factory: RealisticStreetAddress },
    { name: 'RealisticCity', factory: RealisticCity },
    { name: 'RealisticState', factory: RealisticState },
    { name: 'RealisticZipCode', factory: RealisticZipCode },
    { name: 'RealisticUSPhone', factory: RealisticUSPhone },
    { name: 'CompanyName', factory: CompanyName },
    { name: 'ProductName', factory: ProductName },
    { name: 'RecentDate', factory: RecentDate },
    { name: 'FutureDate', factory: FutureDate },
    { name: 'RealisticPrice', factory: RealisticPrice },
  ];

  presets.forEach(({ name, factory }) => {
    it(`${name}: generated values should always validate`, () => {
      const validator = factory();
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator);
        const result = validator.validate(value);
        if (!result.valid) {
          throw new Error(
            `${name}: Generated value failed validation.\n` +
            `  Value: ${JSON.stringify(value)}\n` +
            `  Error: ${result.error}`
          );
        }
      }
    });
  });
});

