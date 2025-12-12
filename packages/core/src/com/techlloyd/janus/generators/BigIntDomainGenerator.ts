import { Domain, BigIntDomain } from '../Domain';
import { RNG } from '../RNG';
import { DomainGeneratorStrategy } from './DomainGeneratorStrategy';

/**
 * Strategy for generating values from a BigInt domain
 * Generates random bigint values within the specified range
 */
export class BigIntDomainGenerator implements DomainGeneratorStrategy<bigint> {
  generate(domain: Domain<bigint>, rng: RNG): bigint {
    const bigIntDomain = domain as BigIntDomain;
    const min = bigIntDomain.min;
    const max = bigIntDomain.max;
    
    // Calculate the range size
    const range = max - min + 1n;
    
    // For small ranges, use simple random
    if (range <= BigInt(Number.MAX_SAFE_INTEGER)) {
      const offset = BigInt(Math.floor(rng.random() * Number(range)));
      return min + offset;
    }
    
    // For large ranges, generate random bytes and scale
    // Determine how many bits we need
    const rangeBits = range.toString(2).length;
    const rangeBytes = Math.ceil(rangeBits / 8);
    
    // Generate random bigint by building from random bytes
    let result: bigint;
    do {
      result = 0n;
      for (let i = 0; i < rangeBytes; i++) {
        const byte = BigInt(Math.floor(rng.random() * 256));
        result = (result << 8n) | byte;
      }
      // Mask to the number of bits we need
      const mask = (1n << BigInt(rangeBits)) - 1n;
      result = result & mask;
    } while (result >= range); // Rejection sampling to ensure uniform distribution
    
    return min + result;
  }
}

