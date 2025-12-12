import { QuantifierDomainGenerator } from '@/com/techlloyd/janus/domains/QuantifierDomainGenerator';
import { DomainGeneratorStrategyRegistry } from '@/com/techlloyd/janus/domains/DomainGeneratorStrategyRegistry';
import { DomainType, type QuantifierDomain, type FiniteDomain } from '@/com/techlloyd/janus/Domain';
import { rngFromSequence } from './helpers';

describe('QuantifierDomainGenerator', () => {
  it('should generate arrays within min/max (bounded)', () => {
    const registry = new DomainGeneratorStrategyRegistry();
    const generator = new QuantifierDomainGenerator(registry);

    const inner: FiniteDomain<string> = { type: DomainType.FINITE_DOMAIN, values: ['x'] as const };
    const domain: QuantifierDomain<string> = {
      type: DomainType.QUANTIFIER_DOMAIN,
      inner,
      min: 2,
      max: 4,
    };

    // rng[0] controls count: range = 3 (2..4). 0 -> min
    const vMin = generator.generate(domain, rngFromSequence([0, 0, 0, 0, 0]));
    expect(vMin).toEqual(['x', 'x']);

    // 0.99 -> max
    const vMax = generator.generate(domain, rngFromSequence([0.99, 0, 0, 0, 0, 0]));
    expect(vMax).toEqual(['x', 'x', 'x', 'x']);
  });

  it('should cap Infinity max at the default (10)', () => {
    const registry = new DomainGeneratorStrategyRegistry();
    const generator = new QuantifierDomainGenerator(registry);

    const inner: FiniteDomain<number> = { type: DomainType.FINITE_DOMAIN, values: [1] as const };
    const domain: QuantifierDomain<number> = {
      type: DomainType.QUANTIFIER_DOMAIN,
      inner,
      min: 0,
      max: Infinity,
    };

    // effectiveMax=10, range=11, 0.99 -> count 10
    const value = generator.generate(domain, rngFromSequence([0.99, ...Array(20).fill(0)]));
    expect(value).toHaveLength(10);
    expect(value.every(v => v === 1)).toBe(true);
  });
});


