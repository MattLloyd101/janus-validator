import { Domain } from "../Domain";
import { CustomGeneratorDomain } from "../domains/CustomGeneratorDomain";
import { DomainGeneratorStrategy } from "./DomainGeneratorStrategy";
import { RNG } from "./RNG";

export class CustomGeneratorDomainGenerator<T> implements DomainGeneratorStrategy<T> {
  generate(domain: Domain<T>, rng: RNG): T {
    const custom = domain as CustomGeneratorDomain<T, Domain<T>>;
    return custom.generate(rng);
  }
}

