import { SequenceDomainGenerator } from '@/com/techlloyd/janus/domains/SequenceDomainGenerator';
import { DomainGeneratorStrategyRegistry } from '@/com/techlloyd/janus/domains/DomainGeneratorStrategyRegistry';
import { DomainType, type SequenceDomain, type FiniteDomain } from '@/com/techlloyd/janus/Domain';
import { rngFromSequence } from './helpers';

describe('SequenceDomainGenerator', () => {
  it('should generate one element per part (in order)', () => {
    const registry = new DomainGeneratorStrategyRegistry();
    const generator = new SequenceDomainGenerator(registry);

    const a: FiniteDomain<string> = { type: DomainType.FINITE_DOMAIN, values: ['a'] as const };
    const one: FiniteDomain<number> = { type: DomainType.FINITE_DOMAIN, values: [1] as const };
    const t: FiniteDomain<boolean> = { type: DomainType.FINITE_DOMAIN, values: [true] as const };

    const domain: SequenceDomain<any> = {
      type: DomainType.SEQUENCE_DOMAIN,
      parts: [a, one, t],
    };

    // Each finite domain consumes one rng.random()
    const value = generator.generate(domain, rngFromSequence([0, 0, 0]));
    expect(value).toEqual(['a', 1, true]);
  });
});


