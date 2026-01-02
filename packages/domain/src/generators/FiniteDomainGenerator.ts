import { Domain } from "../Domain";
import { FiniteDomain } from "../domains/FiniteDomain";
import { DomainGeneratorStrategy } from "./DomainGeneratorStrategy";
import { RNG } from "./RNG";

export class FiniteDomainGenerator<T> implements DomainGeneratorStrategy<T> {
  generate(domain: Domain<T>, rng: RNG): T {
    const finite = domain as FiniteDomain<T>;
    const all = finite.all;
    if (all.length === 0) {
      throw new Error("Cannot generate from empty FiniteDomain");
    }
    const idx = Math.floor(rng.random() * all.length);
    return all[idx] as T;
  }
}

