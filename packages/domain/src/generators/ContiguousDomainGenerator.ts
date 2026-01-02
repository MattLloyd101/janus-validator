import { Domain } from "../Domain";
import { ContiguousDomain } from "../domains/ContiguousDomain";
import { DomainGeneratorStrategy } from "./DomainGeneratorStrategy";
import { RNG } from "./RNG";
import { IntegerInterpolateStrategy } from "./interpolate/IntegerInterpolateStrategy";
import { FloatInterpolateStrategy } from "./interpolate/FloatInterpolateStrategy";

const intInterp = new IntegerInterpolateStrategy();
const floatInterp = new FloatInterpolateStrategy();

export class ContiguousDomainGenerator implements DomainGeneratorStrategy<number | bigint> {
  generate(domain: Domain<number | bigint>, rng: RNG): number | bigint {
    const contiguous = domain as ContiguousDomain<number | bigint>;
    const { min, max } = contiguous;

    if (typeof min === "bigint" || typeof max === "bigint") {
      return this.generateBigInt(min as bigint, max as bigint, rng);
    }

    // Number range
    if (Number.isInteger(min) && Number.isInteger(max)) {
      return intInterp.interpolate(min, max, rng);
    }
    return floatInterp.interpolate(min as number, max as number, rng);
  }

  private generateBigInt(min: bigint, max: bigint, rng: RNG): bigint {
    if (min > max) throw new Error("ContiguousDomain min must be <= max");
    const range = max - min;
    if (range === 0n) return min;
    // If range fits in Number safely, sample uniformly; otherwise fall back to min + random small offset
    if (range <= BigInt(Number.MAX_SAFE_INTEGER)) {
      const offset = BigInt(Math.floor(rng.random() * (Number(range) + 1)));
      return min + offset;
    }
    // Large ranges: sample a 64-bit-ish offset scaled down to range
    const factor = BigInt(Math.floor(rng.random() * 1_000_000));
    return min + (range === 0n ? 0n : (factor % (range + 1n)));
  }
}

