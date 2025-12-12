import { AlternationDomainGenerator } from '@/com/techlloyd/janus/domains/AlternationDomainGenerator';
import { DomainGeneratorStrategyRegistry } from '@/com/techlloyd/janus/domains/DomainGeneratorStrategyRegistry';
import { DomainType, type AlternationDomain, type FiniteDomain } from '@/com/techlloyd/janus/Domain';
import { rngFromSequence } from './helpers';

describe('AlternationDomainGenerator', () => {
  it('should throw when there are no alternatives', () => {
    const registry = new DomainGeneratorStrategyRegistry();
    const generator = new AlternationDomainGenerator(registry);
    const domain: AlternationDomain<string> = {
      type: DomainType.ALTERNATION_DOMAIN,
      alternatives: [],
    };

    expect(() => generator.generate(domain, rngFromSequence([0]))).toThrow(
      'Cannot generate from alternation with no alternatives'
    );
  });

  it('should pick the expected alternative (deterministic)', () => {
    const registry = new DomainGeneratorStrategyRegistry();
    const generator = new AlternationDomainGenerator(registry);

    const a: FiniteDomain<string> = { type: DomainType.FINITE_DOMAIN, values: ['a'] as const };
    const b: FiniteDomain<string> = { type: DomainType.FINITE_DOMAIN, values: ['b'] as const };
    const c: FiniteDomain<string> = { type: DomainType.FINITE_DOMAIN, values: ['c'] as const };

    const domain: AlternationDomain<string> = {
      type: DomainType.ALTERNATION_DOMAIN,
      alternatives: [a, b, c],
    };

    // rng[0] decides alternation index, rng[1] decides finite-domain index
    expect(generator.generate(domain, rngFromSequence([0.0, 0.0]))).toBe('a');
    expect(generator.generate(domain, rngFromSequence([0.34, 0.0]))).toBe('b'); // floor(0.34*3)=1
    expect(generator.generate(domain, rngFromSequence([0.99, 0.0]))).toBe('c'); // floor(0.99*3)=2
  });
});


