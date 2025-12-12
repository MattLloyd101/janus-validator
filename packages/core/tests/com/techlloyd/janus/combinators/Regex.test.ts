import { Regex } from '@/com/techlloyd/janus/combinators/Regex';
import { Generator, RNG, DomainType, RegexDomain } from '@/com/techlloyd/janus/index';

describe('Regex validator', () => {
  describe('basic validation', () => {
    it('should validate strings matching a simple pattern', () => {
      const validator = Regex(/^hello$/);
      expect(validator.validate('hello').valid).toBe(true);
      expect(validator.validate('world').valid).toBe(false);
      expect(validator.validate('hello world').valid).toBe(false);
    });

    it('should reject non-string values', () => {
      const validator = Regex(/\d+/);
      expect(validator.validate(123).valid).toBe(false);
      expect(validator.validate(null).valid).toBe(false);
      expect(validator.validate(undefined).valid).toBe(false);
      expect(validator.validate({}).valid).toBe(false);
    });

    it('should accept string patterns', () => {
      const validator = Regex('^\\d+$');
      expect(validator.validate('123').valid).toBe(true);
      expect(validator.validate('abc').valid).toBe(false);
    });

    it('should reject unsupported regex flags for cross-language portability', () => {
      // Flags are not supported to ensure portable regex semantics across languages
      expect(() => Regex('^hello$', 'i')).toThrow('Unsupported regex flags');
    });

    it('should handle case-insensitive matching via explicit character classes', () => {
      // Instead of /i flag, use explicit character classes for portability
      const validator = Regex('^[hH][eE][lL][lL][oO]$');
      expect(validator.validate('hello').valid).toBe(true);
      expect(validator.validate('HELLO').valid).toBe(true);
      expect(validator.validate('HeLLo').valid).toBe(true);
    });

    it('should provide meaningful error messages', () => {
      const validator = Regex(/^test$/);
      const result = validator.validate('not test');
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('does not match pattern');
      }
    });
  });

  describe('pattern types', () => {
    it('should validate digit patterns', () => {
      const validator = Regex(/^\d{3}-\d{4}$/);
      expect(validator.validate('123-4567').valid).toBe(true);
      expect(validator.validate('12-4567').valid).toBe(false);
      expect(validator.validate('abc-defg').valid).toBe(false);
    });

    it('should validate word patterns', () => {
      const validator = Regex(/^\w+$/);
      expect(validator.validate('hello_world').valid).toBe(true);
      expect(validator.validate('123abc').valid).toBe(true);
      expect(validator.validate('hello world').valid).toBe(false);
    });

    it('should validate alternation patterns', () => {
      const validator = Regex(/^(cat|dog|bird)$/);
      expect(validator.validate('cat').valid).toBe(true);
      expect(validator.validate('dog').valid).toBe(true);
      expect(validator.validate('bird').valid).toBe(true);
      expect(validator.validate('fish').valid).toBe(false);
    });

    it('should validate character class patterns', () => {
      const validator = Regex(/^[aeiou]+$/);
      expect(validator.validate('aeiou').valid).toBe(true);
      expect(validator.validate('bcdfg').valid).toBe(false);
    });
  });

  describe('domain', () => {
    it('should expose a regex domain', () => {
      const validator = Regex(/^test$/);
      expect(validator.domain).toBeDefined();
      expect(validator.domain.type).toBe(DomainType.REGEX_DOMAIN);
      const regexDomain = validator.domain as RegexDomain;
      expect(regexDomain.pattern).toEqual(/^test$/);
      expect(regexDomain.source).toBe('^test$');
    });

    it('should preserve pattern source', () => {
      const validator = Regex(/^[a-z]+\d{2,4}$/);
      const regexDomain = validator.domain as RegexDomain;
      expect(regexDomain.source).toBe('^[a-z]+\\d{2,4}$');
    });
  });
});

describe('Regex generation', () => {
  describe('basic patterns', () => {
    it('should generate strings matching literal pattern', () => {
      const validator = Regex(/^hello$/);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 10; i++) {
        const value = generator.generate(validator.domain);
        expect(value).toBe('hello');
        expect(validator.validate(value).valid).toBe(true);
      }
    });

    it('should generate strings matching digit pattern', () => {
      const validator = Regex(/^\d{3}$/);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 50; i++) {
        const value = generator.generate(validator.domain);
        expect(value).toMatch(/^\d{3}$/);
        expect(validator.validate(value).valid).toBe(true);
      }
    });

    it('should generate strings matching word pattern', () => {
      const validator = Regex(/^\w{5}$/);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 50; i++) {
        const value = generator.generate(validator.domain);
        expect(value).toMatch(/^\w{5}$/);
        expect(validator.validate(value).valid).toBe(true);
      }
    });
  });

  describe('quantifiers', () => {
    it('should generate strings with * quantifier', () => {
      const validator = Regex(/^a*$/);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 50; i++) {
        const value = generator.generate(validator.domain);
        expect(value).toMatch(/^a*$/);
        expect(validator.validate(value).valid).toBe(true);
      }
    });

    it('should generate strings with + quantifier', () => {
      const validator = Regex(/^a+$/);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 50; i++) {
        const value = generator.generate(validator.domain);
        expect(value.length).toBeGreaterThan(0);
        expect(value).toMatch(/^a+$/);
        expect(validator.validate(value).valid).toBe(true);
      }
    });

    it('should generate strings with ? quantifier', () => {
      const validator = Regex(/^ab?c$/);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      const values = new Set<string>();
      for (let i = 0; i < 100; i++) {
        values.add(generator.generate(validator.domain));
      }
      // Should generate both 'ac' and 'abc'
      expect(values.has('ac') || values.has('abc')).toBe(true);
    });

    it('should generate strings with {n} quantifier', () => {
      const validator = Regex(/^x{5}$/);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 10; i++) {
        const value = generator.generate(validator.domain);
        expect(value).toBe('xxxxx');
      }
    });

    it('should generate strings with {n,m} quantifier', () => {
      const validator = Regex(/^a{2,4}$/);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 50; i++) {
        const value = generator.generate(validator.domain);
        expect(value.length).toBeGreaterThanOrEqual(2);
        expect(value.length).toBeLessThanOrEqual(4);
        expect(value).toMatch(/^a{2,4}$/);
      }
    });
  });

  describe('character classes', () => {
    it('should generate strings from character class', () => {
      const validator = Regex(/^[abc]{3}$/);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 50; i++) {
        const value = generator.generate(validator.domain);
        expect(value).toMatch(/^[abc]{3}$/);
        expect(validator.validate(value).valid).toBe(true);
      }
    });

    it('should generate strings from range character class', () => {
      const validator = Regex(/^[a-f]{4}$/);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 50; i++) {
        const value = generator.generate(validator.domain);
        expect(value).toMatch(/^[a-f]{4}$/);
        expect(validator.validate(value).valid).toBe(true);
      }
    });

    it('should generate strings from negated character class', () => {
      const validator = Regex(/^[^0-9]{3}$/);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 50; i++) {
        const value = generator.generate(validator.domain);
        expect(value).toMatch(/^[^0-9]{3}$/);
        expect(validator.validate(value).valid).toBe(true);
      }
    });
  });

  describe('alternation', () => {
    it('should generate strings from alternation', () => {
      const validator = Regex(/^(cat|dog|bird)$/);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      const values = new Set<string>();
      for (let i = 0; i < 100; i++) {
        const value = generator.generate(validator.domain);
        values.add(value);
        expect(validator.validate(value).valid).toBe(true);
      }
      // Should generate multiple different options
      expect(values.size).toBeGreaterThan(1);
    });
  });

  describe('groups', () => {
    it('should generate strings with groups', () => {
      const validator = Regex(/^(ab)+$/);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 50; i++) {
        const value = generator.generate(validator.domain);
        expect(value.length).toBeGreaterThan(0);
        expect(value).toMatch(/^(ab)+$/);
        expect(validator.validate(value).valid).toBe(true);
      }
    });

    it('should generate strings with non-capturing groups', () => {
      const validator = Regex(/^(?:ab)+$/);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 50; i++) {
        const value = generator.generate(validator.domain);
        expect(value.length).toBeGreaterThan(0);
        expect(value).toMatch(/^(?:ab)+$/);
        expect(validator.validate(value).valid).toBe(true);
      }
    });
  });

  describe('any character', () => {
    it('should generate strings with any character', () => {
      const validator = Regex(/^...$/);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 50; i++) {
        const value = generator.generate(validator.domain);
        expect(value.length).toBe(3);
        expect(validator.validate(value).valid).toBe(true);
      }
    });
  });

  describe('complex patterns', () => {
    it('should generate phone number like patterns', () => {
      const validator = Regex(/^\d{3}-\d{3}-\d{4}$/);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 50; i++) {
        const value = generator.generate(validator.domain);
        expect(value).toMatch(/^\d{3}-\d{3}-\d{4}$/);
        expect(validator.validate(value).valid).toBe(true);
      }
    });

    it('should generate simple email like patterns', () => {
      const validator = Regex(/^[a-z]+@[a-z]+\.[a-z]{2,3}$/);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 50; i++) {
        const value = generator.generate(validator.domain);
        expect(value).toMatch(/^[a-z]+@[a-z]+\.[a-z]{2,3}$/);
        expect(validator.validate(value).valid).toBe(true);
      }
    });

    it('should generate hex color like patterns', () => {
      const validator = Regex(/^#[0-9a-f]{6}$/);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 50; i++) {
        const value = generator.generate(validator.domain);
        expect(value).toMatch(/^#[0-9a-f]{6}$/);
        expect(validator.validate(value).valid).toBe(true);
      }
    });
  });
});

describe('property: generated values always validate', () => {
  it('should satisfy: all generated values pass validation', () => {
    const patterns = [
      /^hello$/,
      /^\d{3}$/,
      /^\w+$/,
      /^[a-z]{2,5}$/,
      /^(foo|bar|baz)$/,
      /^a+b*c?$/,
      /^\d{3}-\d{4}$/,
      /^[A-Z][a-z]+$/,
    ];

    const rng: RNG = { random: () => Math.random() };

    for (const pattern of patterns) {
      const validator = Regex(pattern);
      const generator = new Generator(rng);

      for (let i = 0; i < 100; i++) {
        const value = generator.generate(validator.domain);
        const result = validator.validate(value);
        expect(result.valid).toBe(true);
      }
    }
  });
});

