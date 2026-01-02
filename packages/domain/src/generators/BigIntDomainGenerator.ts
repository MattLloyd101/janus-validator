import { Domain } from "../Domain";
import { BigIntDomain } from "../domains/BigIntDomain";
import { DomainGeneratorStrategy } from "./DomainGeneratorStrategy";
import { RNG } from "./RNG";

export class BigIntDomainGenerator implements DomainGeneratorStrategy<bigint> {
  generate(domain: Domain<bigint>, rng: RNG): bigint {
    const big = domain as BigIntDomain;
    const { min, max } = big;
    if (min === max) return min;
    const range = max - min;
    if (range <= BigInt(Number.MAX_SAFE_INTEGER)) {
      const offset = BigInt(Math.floor(rng.random() * (Number(range) + 1)));
      return min + offset;
    }
    const factor = BigInt(Math.floor(rng.random() * 1_000_000));
    return min + (factor % (range + 1n));
  }
}

