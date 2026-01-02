import { Domain } from "../Domain";
import { BytesDomain } from "../domains/BytesDomain";
import { DomainGeneratorStrategy } from "./DomainGeneratorStrategy";
import { RNG } from "./RNG";

export class BytesDomainGenerator implements DomainGeneratorStrategy<Uint8Array> {
  generate(domain: Domain<Uint8Array>, rng: RNG): Uint8Array {
    const bytes = domain as BytesDomain;
    const length =
      bytes.minLength +
      Math.floor(rng.random() * (bytes.maxLength - bytes.minLength + 1));
    const arr = new Uint8Array(length);
    for (let i = 0; i < length; i++) {
      arr[i] = Math.floor(rng.random() * 256);
    }
    return arr;
  }
}

