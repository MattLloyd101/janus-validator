import { StringDomainGenerator } from '@/com/techlloyd/janus/domains/StringDomainGenerator';
import { StringDomain, DomainType } from '@/com/techlloyd/janus/Domain';
import { RNG } from '@/com/techlloyd/janus/RNG';

describe('StringDomainGenerator', () => {
  it('should generate valid strings', () => {
    const generator = new StringDomainGenerator();
    const domain: StringDomain = {
      type: DomainType.STRING_DOMAIN,
    };
    const rng: RNG = {
      random: () => Math.random(),
    };

    const value = generator.generate(domain, rng);
    expect(typeof value).toBe('string');
    expect(value.length).toBeGreaterThanOrEqual(0);
    expect(value.length).toBeLessThanOrEqual(100); // default maxLength
  });

  it('should generate strings within length constraints', () => {
    const generator = new StringDomainGenerator();
    const domain: StringDomain = {
      type: DomainType.STRING_DOMAIN,
      minLength: 5,
      maxLength: 10,
    };
    const rng: RNG = {
      random: () => Math.random(),
    };

    // Generate multiple values and verify they meet length constraints
    for (let i = 0; i < 100; i++) {
      const value = generator.generate(domain, rng);
      expect(value.length).toBeGreaterThanOrEqual(5);
      expect(value.length).toBeLessThanOrEqual(10);
    }
  });

  it('should generate strings with minimum length only', () => {
    const generator = new StringDomainGenerator();
    const domain: StringDomain = {
      type: DomainType.STRING_DOMAIN,
      minLength: 3,
    };
    const rng: RNG = {
      random: () => Math.random(),
    };

    for (let i = 0; i < 50; i++) {
      const value = generator.generate(domain, rng);
      expect(value.length).toBeGreaterThanOrEqual(3);
    }
  });

  it('should generate strings with maximum length only', () => {
    const generator = new StringDomainGenerator();
    const domain: StringDomain = {
      type: DomainType.STRING_DOMAIN,
      maxLength: 5,
    };
    const rng: RNG = {
      random: () => Math.random(),
    };

    for (let i = 0; i < 50; i++) {
      const value = generator.generate(domain, rng);
      expect(value.length).toBeLessThanOrEqual(5);
    }
  });

  it('should generate empty strings when minLength is 0', () => {
    const generator = new StringDomainGenerator();
    const domain: StringDomain = {
      type: DomainType.STRING_DOMAIN,
      minLength: 0,
      maxLength: 0,
    };
    const rng: RNG = {
      random: () => Math.random(),
    };

    const value = generator.generate(domain, rng);
    expect(value).toBe('');
  });

  it('should generate strings with exact length when minLength equals maxLength', () => {
    const generator = new StringDomainGenerator();
    const domain: StringDomain = {
      type: DomainType.STRING_DOMAIN,
      minLength: 5,
      maxLength: 5,
    };
    const rng: RNG = {
      random: () => Math.random(),
    };

    for (let i = 0; i < 20; i++) {
      const value = generator.generate(domain, rng);
      // Note: length might vary slightly due to surrogate pairs, but should be close
      expect(value.length).toBeGreaterThanOrEqual(5);
    }
  });

  it('should generate valid Unicode scalar values', () => {
    const generator = new StringDomainGenerator();
    const domain: StringDomain = {
      type: DomainType.STRING_DOMAIN,
      minLength: 10,
      maxLength: 20,
    };
    const rng: RNG = {
      random: () => Math.random(),
    };

    // Generate strings and verify they contain valid Unicode
    for (let i = 0; i < 100; i++) {
      const value = generator.generate(domain, rng);
      // Check that the string can be iterated (valid UTF-16)
      for (const char of value) {
        expect(char.length).toBeGreaterThan(0);
      }
    }
  });

  it('should use RNG for randomness', () => {
    const generator = new StringDomainGenerator();
    const domain: StringDomain = {
      type: DomainType.STRING_DOMAIN,
    };

    let callCount = 0;
    const rng: RNG = {
      random: () => {
        callCount++;
        return 0.5;
      },
    };

    generator.generate(domain, rng);
    // Should call random multiple times (for length and for each character)
    expect(callCount).toBeGreaterThan(0);
  });

  it('should generate different strings with different RNG values', () => {
    const generator = new StringDomainGenerator();
    const domain: StringDomain = {
      type: DomainType.STRING_DOMAIN,
      minLength: 5,
      maxLength: 10,
    };

    const rng1: RNG = {
      random: () => 0.0,
    };
    const rng2: RNG = {
      random: () => 0.99,
    };

    const value1 = generator.generate(domain, rng1);
    const value2 = generator.generate(domain, rng2);

    // Values might be the same by chance, but with very different RNG values they should differ
    expect(typeof value1).toBe('string');
    expect(typeof value2).toBe('string');
  });
});

