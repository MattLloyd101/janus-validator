import { Domain, DomainType } from '../Domain';
import { RNG } from '../RNG';
import { DomainGeneratorStrategy } from './DomainGeneratorStrategy';
import { FiniteDomainGenerator } from './FiniteDomainGenerator';
import { StringDomainGenerator } from './StringDomainGenerator';
import { ContiguousDomainGenerator } from './ContiguousDomainGenerator';
import { RegexDomainGenerator } from './RegexDomainGenerator';
import { AlternationDomainGenerator } from './AlternationDomainGenerator';
import { SequenceDomainGenerator } from './SequenceDomainGenerator';
import { QuantifierDomainGenerator } from './QuantifierDomainGenerator';
import { StructDomainGenerator } from './StructDomainGenerator';
import { CaptureDomainGenerator } from './CaptureDomainGenerator';
import { RefDomainGenerator } from './RefDomainGenerator';
import { CustomGeneratorDomainGenerator } from './CustomGeneratorDomainGenerator';
import { BytesDomainGenerator } from './BytesDomainGenerator';
import { BigIntDomainGenerator } from './BigIntDomainGenerator';

/**
 * Registry that maps domain types to their corresponding generator strategies
 */
export class DomainGeneratorStrategyRegistry {
  private strategies: Map<DomainType, DomainGeneratorStrategy<any>>;

  constructor() {
    this.strategies = new Map();
    this.registerDefaultStrategies();
  }

  /**
   * Registers the default strategies for all domain types
   */
  private registerDefaultStrategies(): void {
    this.strategies.set(DomainType.FINITE_DOMAIN, new FiniteDomainGenerator());
    this.strategies.set(DomainType.STRING_DOMAIN, new StringDomainGenerator());
    this.strategies.set(DomainType.CONTIGUOUS_DOMAIN, new ContiguousDomainGenerator());
    this.strategies.set(DomainType.REGEX_DOMAIN, new RegexDomainGenerator());
    this.strategies.set(DomainType.ALTERNATION_DOMAIN, new AlternationDomainGenerator(this));
    this.strategies.set(DomainType.SEQUENCE_DOMAIN, new SequenceDomainGenerator(this));
    this.strategies.set(DomainType.QUANTIFIER_DOMAIN, new QuantifierDomainGenerator(this));
    this.strategies.set(DomainType.STRUCT_DOMAIN, new StructDomainGenerator(this));
    this.strategies.set(DomainType.CAPTURE_DOMAIN, new CaptureDomainGenerator(this));
    this.strategies.set(DomainType.REF_DOMAIN, new RefDomainGenerator());
    this.strategies.set(DomainType.CUSTOM_GENERATOR_DOMAIN, new CustomGeneratorDomainGenerator());
    this.strategies.set(DomainType.BYTES_DOMAIN, new BytesDomainGenerator());
    this.strategies.set(DomainType.BIGINT_DOMAIN, new BigIntDomainGenerator());
  }

  /**
   * Registers a strategy for a specific domain type
   */
  register<T>(domainType: DomainType, strategy: DomainGeneratorStrategy<T>): void {
    this.strategies.set(domainType, strategy);
  }

  /**
   * Gets the strategy for a specific domain type
   */
  get<T>(domainType: DomainType): DomainGeneratorStrategy<T> {
    const strategy = this.strategies.get(domainType);
    if (!strategy) {
      throw new Error(`No generator strategy registered for domain type: ${domainType}`);
    }
    return strategy;
  }

  /**
   * Generates a value using the appropriate strategy for the domain
   */
  generate<T>(domain: Domain<T>, rng: RNG): T {
    const strategy = this.get<T>(domain.type);
    return strategy.generate(domain, rng);
  }
}

