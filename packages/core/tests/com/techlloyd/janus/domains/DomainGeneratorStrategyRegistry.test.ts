import { DomainGeneratorStrategyRegistry } from '@/com/techlloyd/janus/domains/DomainGeneratorStrategyRegistry';
import { FiniteDomainGenerator } from '@/com/techlloyd/janus/domains/FiniteDomainGenerator';
import { StringDomainGenerator } from '@/com/techlloyd/janus/domains/StringDomainGenerator';
import { DomainGeneratorStrategy } from '@/com/techlloyd/janus/domains/DomainGeneratorStrategy';
import { Domain, DomainType, FiniteDomain, StringDomain } from '@/com/techlloyd/janus/Domain';
import { RNG } from '@/com/techlloyd/janus/RNG';

describe('DomainGeneratorStrategyRegistry', () => {
  it('should register default strategies on construction', () => {
    const registry = new DomainGeneratorStrategyRegistry();
    
    // Should be able to get strategies for default domain types
    expect(registry.get(DomainType.FINITE_DOMAIN)).toBeInstanceOf(FiniteDomainGenerator);
    expect(registry.get(DomainType.STRING_DOMAIN)).toBeInstanceOf(StringDomainGenerator);
  });

  it('should allow registering custom strategies', () => {
    const registry = new DomainGeneratorStrategyRegistry();
    
    const customStrategy: DomainGeneratorStrategy<number> = {
      generate: (_domain: Domain<number>, _rng: RNG): number => {
        return 42;
      },
    };

    registry.register(DomainType.FINITE_DOMAIN, customStrategy);
    
    const domain: FiniteDomain<number> = {
      type: DomainType.FINITE_DOMAIN,
      values: [1, 2, 3] as const,
    };
    const rng: RNG = {
      random: () => Math.random(),
    };

    const value = registry.generate(domain, rng);
    expect(value).toBe(42);
  });

  it('should throw error for unregistered domain type', () => {
    const registry = new DomainGeneratorStrategyRegistry();
    
    // Create a mock domain type that doesn't exist
    const unknownDomain: Domain<string> = {
      type: 'UNKNOWN_DOMAIN' as DomainType,
    };
    const rng: RNG = {
      random: () => Math.random(),
    };

    expect(() => {
      registry.generate(unknownDomain, rng);
    }).toThrow('No generator strategy registered for domain type');
  });

  it('should generate values using registered strategies', () => {
    const registry = new DomainGeneratorStrategyRegistry();
    
    const finiteDomain: FiniteDomain<boolean> = {
      type: DomainType.FINITE_DOMAIN,
      values: [true, false] as const,
    };
    const stringDomain: StringDomain = {
      type: DomainType.STRING_DOMAIN,
      minLength: 2,
      maxLength: 5,
    };
    const rng: RNG = {
      random: () => Math.random(),
    };

    const booleanValue = registry.generate(finiteDomain, rng);
    expect([true, false]).toContain(booleanValue);

    const stringValue = registry.generate<string>(stringDomain, rng);
    expect(typeof stringValue).toBe('string');
    expect(stringValue.length).toBeGreaterThanOrEqual(2);
    expect(stringValue.length).toBeLessThanOrEqual(5);
  });

  it('should allow replacing existing strategies', () => {
    const registry = new DomainGeneratorStrategyRegistry();
    
    const customFiniteStrategy: DomainGeneratorStrategy<string> = {
      generate: (_domain: Domain<string>, _rng: RNG): string => {
        return 'custom';
      },
    };

    registry.register(DomainType.FINITE_DOMAIN, customFiniteStrategy);
    
    const domain: FiniteDomain<string> = {
      type: DomainType.FINITE_DOMAIN,
      values: ['a', 'b', 'c'] as const,
    };
    const rng: RNG = {
      random: () => Math.random(),
    };

    const value = registry.generate(domain, rng);
    expect(value).toBe('custom');
  });

  it('should use correct strategy for each domain type', () => {
    const registry = new DomainGeneratorStrategyRegistry();
    const rng: RNG = {
      random: () => Math.random(),
    };

    // Test finite domain
    const finiteDomain: FiniteDomain<number> = {
      type: DomainType.FINITE_DOMAIN,
      values: [1, 2, 3] as const,
    };
    const finiteValue = registry.generate(finiteDomain, rng);
    expect([1, 2, 3]).toContain(finiteValue);

    // Test String domain
    const stringDomain: StringDomain = {
      type: DomainType.STRING_DOMAIN,
    };
    const stringValue = registry.generate(stringDomain, rng);
    expect(typeof stringValue).toBe('string');
  });
});

