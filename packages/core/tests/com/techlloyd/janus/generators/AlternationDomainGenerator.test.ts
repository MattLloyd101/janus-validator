import { AlternationDomainGenerator } from '@/com/techlloyd/janus/generators/AlternationDomainGenerator';
import { DomainGeneratorStrategyRegistry } from '@/com/techlloyd/janus/generators/DomainGeneratorStrategyRegistry';
import { AlternationDomain, FiniteDomain } from '@/com/techlloyd/janus/Domain';
import { rngFromSequence } from './helpers';

describe('AlternationDomainGenerator', () => {
  it('should throw when there are no alternatives', () => {
    const registry = new DomainGeneratorStrategyRegistry();
    const generator = new AlternationDomainGenerator(registry);
    const domain: AlternationDomain<string> = new AlternationDomain<string>([]);

    expect(() => generator.generate(domain, rngFromSequence([0]))).toThrow(
      'Cannot generate from alternation with no alternatives'
    );
  });

  it('should pick the expected alternative (deterministic)', () => {
    const registry = new DomainGeneratorStrategyRegistry();
    const generator = new AlternationDomainGenerator(registry);

    const a: FiniteDomain<string> = new FiniteDomain(['a'] as const);
    const b: FiniteDomain<string> = new FiniteDomain(['b'] as const);
    const c: FiniteDomain<string> = new FiniteDomain(['c'] as const);

    const domain: AlternationDomain<string> = new AlternationDomain<string>([a, b, c]);

    // rng[0] decides alternation index, rng[1] decides finite-domain index
    expect(generator.generate(domain, rngFromSequence([0.0, 0.0]))).toBe('a');
    expect(generator.generate(domain, rngFromSequence([0.34, 0.0]))).toBe('b'); // floor(0.34*3)=1
    expect(generator.generate(domain, rngFromSequence([0.99, 0.0]))).toBe('c'); // floor(0.99*3)=2
  });
});


