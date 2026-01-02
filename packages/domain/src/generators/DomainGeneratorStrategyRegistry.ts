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

export class DomainGeneratorStrategyRegistry {
  private strategies: Map<DomainType, DomainGeneratorStrategy<unknown>>;

  constructor() {
    this.strategies = new Map();
    this.registerDefaultStrategies();
  }

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
  }

  register<T>(domainType: DomainType, strategy: DomainGeneratorStrategy<T>): void {
    this.strategies.set(domainType, strategy);
  }

  get<T>(domainType: DomainType): DomainGeneratorStrategy<T> {
    const strategy = this.strategies.get(domainType);
    if (!strategy) {
      throw new Error(`No generator strategy registered for domain type: ${domainType}`);
    }
    return strategy as DomainGeneratorStrategy<T>;
  }

  generate<T>(domain: Domain<T>, rng: RNG): T {
    const strategy = this.get<T>(domain.kind);
    return strategy.generate(domain, rng);
  }
}

