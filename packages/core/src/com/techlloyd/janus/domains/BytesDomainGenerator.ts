import { Domain, BytesDomain } from '../Domain';
import { RNG } from '../RNG';
import { DomainGeneratorStrategy } from './DomainGeneratorStrategy';

/**
 * Strategy for generating values from a Bytes domain
 * Generates random Uint8Array of appropriate length
 */
export class BytesDomainGenerator implements DomainGeneratorStrategy<Uint8Array> {
  generate(domain: Domain<Uint8Array>, rng: RNG): Uint8Array {
    const bytesDomain = domain as BytesDomain;
    const minLength = bytesDomain.minLength;
    const maxLength = bytesDomain.maxLength;
    
    // Generate a random length between min and max (inclusive)
    const length = minLength + Math.floor(rng.random() * (maxLength - minLength + 1));
    
    // Create a Uint8Array with random bytes
    const result = new Uint8Array(length);
    for (let i = 0; i < length; i++) {
      result[i] = Math.floor(rng.random() * 256);
    }
    
    return result;
  }
}

