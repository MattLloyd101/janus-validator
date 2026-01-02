import { Domain } from "../Domain";
import { StringDomain } from "../domains/StringDomain";
import { DomainGeneratorStrategy } from "./DomainGeneratorStrategy";
import { RNG } from "./RNG";

const PRINTABLE_ASCII_MIN = 32;
const PRINTABLE_ASCII_MAX = 126;

export class StringDomainGenerator implements DomainGeneratorStrategy<string> {
  generate(domain: Domain<string>, rng: RNG): string {
    const stringDomain = domain as StringDomain;
    const minLength = stringDomain.minLength;
    const maxLength = stringDomain.maxLength;
    const targetLength =
      minLength + Math.floor(rng.random() * (maxLength - minLength + 1));

    let result = "";
    for (let i = 0; i < targetLength; i++) {
      const cp =
        PRINTABLE_ASCII_MIN +
        Math.floor(rng.random() * (PRINTABLE_ASCII_MAX - PRINTABLE_ASCII_MIN + 1));
      result += String.fromCharCode(cp);
    }
    return result;
  }
}

