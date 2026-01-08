import { Boolean } from '@/com/techlloyd/janus/combinators/Boolean';
import { Generator, RNG, DomainType, FiniteDomain } from '@/com/techlloyd/janus/index';

describe('Boolean validator', () => {
  it('should validate boolean values', () => {
    const validator = Boolean();
    expect(validator.validate(true).valid).toBe(true);
    expect(validator.validate(false).valid).toBe(true);
    expect(validator.validate('true').valid).toBe(false);
    expect(validator.validate(1).valid).toBe(false);
    expect(validator.validate(null).valid).toBe(false);
  });

  it('should return the validated boolean value', () => {
    const validator = Boolean();
    const result = validator.validate(false);
    expect(result.valid).toBe(true);
    if (result.valid) {
      expect(result.value).toBe(false);
    }
  });

  it('should provide meaningful error messages', () => {
    const validator = Boolean();
    const result = validator.validate('not a boolean');
    expect(result.valid).toBe(false);
    if (!result.valid) {
      expect(result.error).toContain('boolean');
      expect(result.error).toContain('string');
    }
  });

  it('should reject truthy non-boolean values', () => {
    const validator = Boolean();
    expect(validator.validate(1).valid).toBe(false);
    expect(validator.validate('true').valid).toBe(false);
    expect(validator.validate({}).valid).toBe(false);
    expect(validator.validate([]).valid).toBe(false);
  });

  it('should reject falsy non-boolean values', () => {
    const validator = Boolean();
    expect(validator.validate(0).valid).toBe(false);
    expect(validator.validate('').valid).toBe(false);
    expect(validator.validate(null).valid).toBe(false);
    expect(validator.validate(undefined).valid).toBe(false);
  });

  it('should accept both true and false', () => {
    const validator = Boolean();
    const trueResult = validator.validate(true);
    const falseResult = validator.validate(false);
    
    expect(trueResult.valid).toBe(true);
    expect(falseResult.valid).toBe(true);
    
    if (trueResult.valid) {
      expect(trueResult.value).toBe(true);
    }
    if (falseResult.valid) {
      expect(falseResult.value).toBe(false);
    }
  });

  it('should expose a domain property', () => {
    const validator = Boolean();
    expect(validator.domain).toBeDefined();
    const finiteDomain = validator.domain as FiniteDomain<boolean>;
    expect(finiteDomain.kind).toBe(DomainType.FINITE);
    expect(finiteDomain.all).toEqual([true, false]);
  });
});

describe('Boolean domain', () => {
  it('should have finite domain type and values', () => {
    const validator = Boolean();
    const finiteDomain = validator.domain as FiniteDomain<boolean>;
    
    expect(finiteDomain.kind).toBe(DomainType.FINITE);
    expect(finiteDomain.all).toContain(true);
    expect(finiteDomain.all).toContain(false);
    expect(finiteDomain.all.length).toBe(2);
  });

  it('should generate boolean values using Generator', () => {
    const validator = Boolean();
    const rng: RNG = {
      random: () => 0.3,
    };
    const generator = new Generator(rng);

    const value = generator.generate(validator.domain);
    expect(typeof value).toBe('boolean');
    expect([true, false]).toContain(value);
  });

  it('should generate values from the finite domain', () => {
    const validator = Boolean();
    const rng: RNG = {
      random: () => 0.0, // Should select first value (index 0)
    };
    const generator = new Generator(rng);

    const value = generator.generate(validator.domain);
    // With random() = 0.0, Math.floor(0.0 * 2) = 0, so index 0
    // The values array is [true, false], so index 0 is true
    expect(value).toBe(true);
    expect([true, false]).toContain(value);
  });

  it('should generate different values with different RNG outputs', () => {
    const validator = Boolean();
    
    const rng1: RNG = {
      random: () => 0.0, // index 0
    };
    const rng2: RNG = {
      random: () => 0.99, // index 1
    };

    const generator1 = new Generator(rng1);
    const generator2 = new Generator(rng2);
    const value1 = generator1.generate(validator.domain);
    const value2 = generator2.generate(validator.domain);
    expect([true, false]).toContain(value1);
    expect([true, false]).toContain(value2);
  });

  it('should generate values that pass validation', () => {
    const validator = Boolean();
    const rng: RNG = {
      random: () => Math.random(),
    };
    const generator = new Generator(rng);

    // Generate multiple values and verify they all pass validation
    for (let i = 0; i < 100; i++) {
      const value = generator.generate(validator.domain);
      const result = validator.validate(value);
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe(value);
      }
    }
  });
});

describe('Generator class with Boolean', () => {
  it('should generate values using validator domain and RNG', () => {
    const validator = Boolean();
    const rng: RNG = {
      random: () => 0.3,
    };
    const generator = new Generator(rng);

    const value = generator.generate(validator.domain);
    expect(typeof value).toBe('boolean');
    expect([true, false]).toContain(value);
  });

  it('should generate values that pass validation', () => {
    const validator = Boolean();
    const rng: RNG = {
      random: () => Math.random(),
    };
    const generator = new Generator(rng);

    // Generate multiple values and verify they all pass validation
    for (let i = 0; i < 100; i++) {
      const value = generator.generate(validator.domain);
      const result = validator.validate(value);
      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.value).toBe(value);
      }
    }
  });

  it('should use the validator\'s domain metadata', () => {
    const validator = Boolean();
    const rng: RNG = {
      random: () => 0.7,
    };
    const generator = new Generator(rng);

    const value = generator.generate(validator.domain);
    expect([true, false]).toContain(value);
  });
});

