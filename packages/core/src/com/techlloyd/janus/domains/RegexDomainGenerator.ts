import { Domain, RegexDomain } from '../Domain';
import { RNG } from '../RNG';
import { DomainGeneratorStrategy } from './DomainGeneratorStrategy';
import { parseRegex } from '../combinators/regex/RegexParser';

/**
 * Strategy for generating strings that match a regular expression pattern
 * 
 * This works by:
 * 1. Parsing the regex pattern into a composed tree of RegexValidator instances
 * 2. Using each validator's generate() method to produce matching strings
 * 
 * Each validator in the tree (Literal, CharClass, Sequence, Alternation, etc.)
 * knows how to generate strings that match its pattern.
 */
export class RegexDomainGenerator implements DomainGeneratorStrategy<string> {
  /**
   * Generate a string that matches the regex pattern in the domain
   */
  generate(domain: Domain<string>, rng: RNG): string {
    const regexDomain = domain as RegexDomain;
    
    // Parse the regex source into a composed validator tree
    const validator = parseRegex(regexDomain.source);
    
    // Generate a string using the validator's generate method
    return validator.generate(rng);
  }
}

