import { DomainGeneratorStrategyRegistry } from '@/com/techlloyd/janus/generators/DomainGeneratorStrategyRegistry';
import type { FiniteDomain, CustomGeneratorDomain } from '@/com/techlloyd/janus/Domain';
import { CaptureDomain, CustomGeneratorDomain as CustomGeneratorDomainClass, FiniteDomain as FiniteDomainClass, RefDomain } from '@/com/techlloyd/janus/Domain';
import { rngFromSequence } from './helpers';

describe('Capture/Ref/Custom domain generators', () => {
  it('should generate through CaptureDomain by delegating to inner', () => {
    const registry = new DomainGeneratorStrategyRegistry();

    const inner: FiniteDomain<string> = new FiniteDomainClass(['x'] as const);
    const captureDomain = new CaptureDomain('cap', inner);

    const value = registry.generate(captureDomain as any, rngFromSequence([0]));
    expect(value).toBe('x');
  });

  it('should throw for RefDomain generation', () => {
    const registry = new DomainGeneratorStrategyRegistry();

    const refDomain = new RefDomain('ref');

    expect(() => registry.generate(refDomain as any, rngFromSequence([0]))).toThrow(
      'Cannot generate from RefDomain independently'
    );
  });

  it('should generate from CustomGeneratorDomain by calling its generate()', () => {
    const registry = new DomainGeneratorStrategyRegistry();

    const innerDomain: FiniteDomain<number> = new FiniteDomainClass([1] as const);

    const domain: CustomGeneratorDomain<number> = new CustomGeneratorDomainClass(innerDomain, () => 123) as any;

    const value = registry.generate(domain, rngFromSequence([0]));
    expect(value).toBe(123);
  });
});


