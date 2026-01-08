import { Domain } from "../Domain";
import { DomainType } from "../types";
import { RNG } from "./RNG";
import { DomainGeneratorStrategy } from "./DomainGeneratorStrategy";
import { FiniteDomainGenerator } from "./FiniteDomainGenerator";
import { StringDomainGenerator } from "./StringDomainGenerator";
import { ContiguousDomainGenerator } from "./ContiguousDomainGenerator";
import { RegexDomainGenerator } from "./RegexDomainGenerator";
import { AlternationDomainGenerator } from "./AlternationDomainGenerator";
import { SequenceDomainGenerator } from "./SequenceDomainGenerator";
import { QuantifierDomainGenerator } from "./QuantifierDomainGenerator";
import { StructDomainGenerator } from "./StructDomainGenerator";
import { CustomGeneratorDomainGenerator } from "./CustomGeneratorDomainGenerator";
import { BytesDomainGenerator } from "./BytesDomainGenerator";
import { BigIntDomainGenerator } from "./BigIntDomainGenerator";
import { TransformDomainGenerator } from "./TransformDomainGenerator";

/**
 * Registry that maps domain types to their corresponding generator strategies.
 * 
 * The registry uses the Strategy pattern to decouple domain value generation
 * from the domain types themselves. Each domain type has a registered strategy
 * that knows how to generate valid values for that domain.
 * 
 * ## Default Strategies
 * 
 * The registry comes pre-configured with strategies for all built-in domain types:
 * - `FINITE` → `FiniteDomainGenerator` (picks from discrete values)
 * - `STRING` → `StringDomainGenerator` (generates Unicode strings)
 * - `CONTIGUOUS` → `ContiguousDomainGenerator` (generates numbers in range)
 * - `REGEX` → `RegexDomainGenerator` (generates matching strings)
 * - `ALTERNATION` → `AlternationDomainGenerator` (picks from alternatives)
 * - `SEQUENCE` → `SequenceDomainGenerator` (generates tuples)
 * - `QUANTIFIER` → `QuantifierDomainGenerator` (generates arrays)
 * - `STRUCT` → `StructDomainGenerator` (generates objects)
 * - `CUSTOM_GENERATOR` → `CustomGeneratorDomainGenerator` (uses custom function)
 * - `BYTES` → `BytesDomainGenerator` (generates binary data)
 * - `BIGINT` → `BigIntDomainGenerator` (generates BigInt values)
 * - `TRANSFORM` → `TransformDomainGenerator` (generates then transforms)
 * 
 * ## Custom Strategies
 * 
 * You can override the default strategy for any domain type using `register()`:
 * 
 * ```typescript
 * const registry = new DomainGeneratorStrategyRegistry();
 * registry.register(DomainType.STRING, new MyCustomStringGenerator());
 * ```
 * 
 * @example
 * ```typescript
 * const registry = new DomainGeneratorStrategyRegistry();
 * const rng = { random: Math.random };
 * 
 * const domain = new ContiguousDomain(0, 100);
 * const value = registry.generate(domain, rng); // Returns number between 0-100
 * ```
 */
export class DomainGeneratorStrategyRegistry {
  private strategies: Map<DomainType, DomainGeneratorStrategy<unknown>>;

  constructor() {
    this.strategies = new Map();
    this.registerDefaultStrategies();
  }

  /**
   * Registers the default generator strategies for all built-in domain types.
   * Called automatically during construction.
   */
  private registerDefaultStrategies(): void {
    this.strategies.set(DomainType.FINITE, new FiniteDomainGenerator());
    this.strategies.set(DomainType.STRING, new StringDomainGenerator());
    this.strategies.set(DomainType.CONTIGUOUS, new ContiguousDomainGenerator());
    this.strategies.set(DomainType.REGEX, new RegexDomainGenerator());
    this.strategies.set(DomainType.ALTERNATION, new AlternationDomainGenerator(this));
    this.strategies.set(DomainType.SEQUENCE, new SequenceDomainGenerator(this));
    this.strategies.set(DomainType.QUANTIFIER, new QuantifierDomainGenerator(this));
    this.strategies.set(DomainType.STRUCT, new StructDomainGenerator(this));
    this.strategies.set(DomainType.CUSTOM_GENERATOR, new CustomGeneratorDomainGenerator());
    this.strategies.set(DomainType.BYTES, new BytesDomainGenerator());
    this.strategies.set(DomainType.BIGINT, new BigIntDomainGenerator());
    this.strategies.set(DomainType.TRANSFORM, new TransformDomainGenerator(this));
  }

  /**
   * Registers a custom generator strategy for a domain type.
   * 
   * This will override any previously registered strategy for this domain type,
   * including the default strategies.
   * 
   * @param domainType - The domain type to register a strategy for
   * @param strategy - The generator strategy to use for this domain type
   * 
   * @example
   * ```typescript
   * registry.register(DomainType.STRING, new MyFasterStringGenerator());
   * ```
   */
  register<T>(domainType: DomainType, strategy: DomainGeneratorStrategy<T>): void {
    this.strategies.set(domainType, strategy);
  }

  /**
   * Retrieves the generator strategy for a domain type.
   * 
   * @param domainType - The domain type to get a strategy for
   * @returns The registered generator strategy
   * @throws Error if no strategy is registered for the given domain type
   */
  get<T>(domainType: DomainType): DomainGeneratorStrategy<T> {
    const strategy = this.strategies.get(domainType);
    if (!strategy) {
      throw new Error(`No generator strategy registered for domain type: ${domainType}`);
    }
    return strategy as DomainGeneratorStrategy<T>;
  }

  /**
   * Generates a value for the given domain using the appropriate strategy.
   * 
   * This is the primary entry point for value generation. It looks up the
   * strategy for the domain's type and delegates generation to it.
   * 
   * @param domain - The domain to generate a value for
   * @param rng - Random number generator to use
   * @returns A value that belongs to the domain
   * @throws Error if no strategy is registered for the domain's type
   * 
   * @example
   * ```typescript
   * const domain = new FiniteDomain(['red', 'green', 'blue']);
   * const color = registry.generate(domain, rng); // 'red', 'green', or 'blue'
   * ```
   */
  generate<T>(domain: Domain<T>, rng: RNG): T {
    const strategy = this.get<T>(domain.kind);
    return strategy.generate(domain, rng);
  }
}
