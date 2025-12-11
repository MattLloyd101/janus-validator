import { FiniteDomainGenerator } from '@/com/techlloyd/janus/domains/FiniteDomainGenerator';
import { FiniteDomain, DomainType } from '@/com/techlloyd/janus/Domain';
import { RNG } from '@/com/techlloyd/janus/RNG';

describe('FiniteDomainGenerator', () => {
  it('should generate values from a finite domain', () => {
    const generator = new FiniteDomainGenerator<boolean>();
    const domain: FiniteDomain<boolean> = {
      type: DomainType.FINITE_DOMAIN,
      values: [true, false] as const,
    };
    const rng: RNG = {
      random: () => 0.3,
    };

    const value = generator.generate(domain, rng);
    expect([true, false]).toContain(value);
  });

  it('should select first value when RNG returns 0', () => {
    const generator = new FiniteDomainGenerator<string>();
    const domain: FiniteDomain<string> = {
      type: DomainType.FINITE_DOMAIN,
      values: ['a', 'b', 'c'] as const,
    };
    const rng: RNG = {
      random: () => 0.0,
    };

    const value = generator.generate(domain, rng);
    expect(value).toBe('a');
  });

  it('should select last value when RNG returns value close to 1', () => {
    const generator = new FiniteDomainGenerator<number>();
    const domain: FiniteDomain<number> = {
      type: DomainType.FINITE_DOMAIN,
      values: [1, 2, 3, 4, 5] as const,
    };
    const rng: RNG = {
      random: () => 0.99,
    };

    const value = generator.generate(domain, rng);
    // With 5 values, index = floor(0.99 * 5) = floor(4.95) = 4
    expect(value).toBe(5);
  });

  it('should generate values from single-element domain', () => {
    const generator = new FiniteDomainGenerator<string>();
    const domain: FiniteDomain<string> = {
      type: DomainType.FINITE_DOMAIN,
      values: ['only'] as const,
    };
    const rng: RNG = {
      random: () => Math.random(),
    };

    const value = generator.generate(domain, rng);
    expect(value).toBe('only');
  });

  it('should generate all values from domain over many iterations', () => {
    const generator = new FiniteDomainGenerator<string>();
    const domain: FiniteDomain<string> = {
      type: DomainType.FINITE_DOMAIN,
      values: ['a', 'b', 'c'] as const,
    };
    const rng: RNG = {
      random: () => Math.random(),
    };

    const generatedValues = new Set<string>();
    for (let i = 0; i < 1000; i++) {
      generatedValues.add(generator.generate(domain, rng));
    }

    // Should have generated all values
    expect(generatedValues.has('a')).toBe(true);
    expect(generatedValues.has('b')).toBe(true);
    expect(generatedValues.has('c')).toBe(true);
  });

  it('should use RNG to determine selection', () => {
    const generator = new FiniteDomainGenerator<number>();
    const domain: FiniteDomain<number> = {
      type: DomainType.FINITE_DOMAIN,
      values: [10, 20, 30] as const,
    };

    let callCount = 0;
    const rng: RNG = {
      random: () => {
        callCount++;
        return 0.5;
      },
    };

    generator.generate(domain, rng);
    expect(callCount).toBe(1);
  });

  it('should handle large finite domains', () => {
    const generator = new FiniteDomainGenerator<number>();
    const values = Array.from({ length: 1000 }, (_, i) => i);
    const domain: FiniteDomain<number> = {
      type: DomainType.FINITE_DOMAIN,
      values: values as readonly number[],
    };
    const rng: RNG = {
      random: () => Math.random(),
    };

    const value = generator.generate(domain, rng);
    expect(value).toBeGreaterThanOrEqual(0);
    expect(value).toBeLessThan(1000);
    expect(Number.isInteger(value)).toBe(true);
  });
});

