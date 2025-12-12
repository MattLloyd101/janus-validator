import { StructDomainGenerator } from '@/com/techlloyd/janus/generators/StructDomainGenerator';
import { DomainGeneratorStrategyRegistry } from '@/com/techlloyd/janus/generators/DomainGeneratorStrategyRegistry';
import { FiniteDomain, StructDomain } from '@/com/techlloyd/janus/Domain';
import { rngFromSequence } from './helpers';

describe('StructDomainGenerator', () => {
  it('should generate all properties from the schema (ignores strict)', () => {
    const registry = new DomainGeneratorStrategyRegistry();
    const generator = new StructDomainGenerator(registry);

    const name: FiniteDomain<string> = new FiniteDomain(['Alice'] as const);
    const age: FiniteDomain<number> = new FiniteDomain([42] as const);

    const domain = new StructDomain({ name, age }, true);

    // Each finite domain consumes one rng.random()
    const value = generator.generate(domain as any, rngFromSequence([0, 0]));
    expect(value).toEqual({ name: 'Alice', age: 42 });
  });
});


