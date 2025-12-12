import { DomainGeneratorStrategyRegistry } from '@/com/techlloyd/janus/domains/DomainGeneratorStrategyRegistry';
import { DomainType, type FiniteDomain } from '@/com/techlloyd/janus/Domain';
import type { CustomGeneratorDomain } from '@/com/techlloyd/janus/combinators/WithGenerator';
import { rngFromSequence } from './helpers';

describe('Capture/Ref/Custom domain generators', () => {
  it('should generate through CaptureDomain by delegating to inner', () => {
    const registry = new DomainGeneratorStrategyRegistry();

    const inner: FiniteDomain<string> = { type: DomainType.FINITE_DOMAIN, values: ['x'] as const };
    const captureDomain = {
      type: DomainType.CAPTURE_DOMAIN,
      name: 'cap',
      inner,
    };

    const value = registry.generate(captureDomain as any, rngFromSequence([0]));
    expect(value).toBe('x');
  });

  it('should throw for RefDomain generation', () => {
    const registry = new DomainGeneratorStrategyRegistry();

    const refDomain = {
      type: DomainType.REF_DOMAIN,
      name: 'ref',
    };

    expect(() => registry.generate(refDomain as any, rngFromSequence([0]))).toThrow(
      'Cannot generate from RefDomain independently'
    );
  });

  it('should generate from CustomGeneratorDomain by calling its generate()', () => {
    const registry = new DomainGeneratorStrategyRegistry();

    const innerDomain: FiniteDomain<number> = {
      type: DomainType.FINITE_DOMAIN,
      values: [1] as const,
    };

    const domain: CustomGeneratorDomain<number> = {
      type: DomainType.CUSTOM_GENERATOR_DOMAIN,
      innerDomain,
      generate: () => 123,
    };

    const value = registry.generate(domain, rngFromSequence([0]));
    expect(value).toBe(123);
  });
});


