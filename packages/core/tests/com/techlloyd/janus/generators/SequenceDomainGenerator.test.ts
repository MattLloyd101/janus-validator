import { SequenceDomainGenerator } from '@/com/techlloyd/janus/generators/SequenceDomainGenerator';
import { DomainGeneratorStrategyRegistry } from '@/com/techlloyd/janus/generators/DomainGeneratorStrategyRegistry';
import { FiniteDomain, SequenceDomain } from '@/com/techlloyd/janus/Domain';
import { rngFromSequence } from './helpers';

describe('SequenceDomainGenerator', () => {
  it('should generate one element per part (in order)', () => {
    const registry = new DomainGeneratorStrategyRegistry();
    const generator = new SequenceDomainGenerator(registry);

    const a: FiniteDomain<string> = new FiniteDomain(['a'] as const);
    const one: FiniteDomain<number> = new FiniteDomain([1] as const);
    const t: FiniteDomain<boolean> = new FiniteDomain([true] as const);

    const domain: SequenceDomain<any> = new SequenceDomain<any>([a, one, t]);

    // Each finite domain consumes one rng.random()
    const value = generator.generate(domain, rngFromSequence([0, 0, 0]));
    expect(value).toEqual(['a', 1, true]);
  });
});


