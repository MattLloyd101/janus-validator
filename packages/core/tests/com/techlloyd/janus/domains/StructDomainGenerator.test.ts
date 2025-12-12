import { StructDomainGenerator } from '@/com/techlloyd/janus/domains/StructDomainGenerator';
import { DomainGeneratorStrategyRegistry } from '@/com/techlloyd/janus/domains/DomainGeneratorStrategyRegistry';
import { DomainType, type FiniteDomain } from '@/com/techlloyd/janus/Domain';
import { rngFromSequence } from './helpers';

describe('StructDomainGenerator', () => {
  it('should generate all properties from the schema (ignores strict)', () => {
    const registry = new DomainGeneratorStrategyRegistry();
    const generator = new StructDomainGenerator(registry);

    const name: FiniteDomain<string> = { type: DomainType.FINITE_DOMAIN, values: ['Alice'] as const };
    const age: FiniteDomain<number> = { type: DomainType.FINITE_DOMAIN, values: [42] as const };

    const domain = {
      type: DomainType.STRUCT_DOMAIN,
      schema: { name, age },
      strict: true,
    };

    // Each finite domain consumes one rng.random()
    const value = generator.generate(domain as any, rngFromSequence([0, 0]));
    expect(value).toEqual({ name: 'Alice', age: 42 });
  });
});


