import { CharSetDomain, Domain, StringDomain } from '../Domain';
import { RNG } from '../RNG';
import { DomainGeneratorStrategy } from './DomainGeneratorStrategy';

/**
 * A string part for generation - either a literal string or a domain
 */
type StringPart = string | Domain<string>;

/**
 * Extended domain type that includes compound string parts
 */
interface CompoundStringDomain extends StringDomain {
  _parts?: StringPart[];
}

/**
 * Generates a valid Unicode scalar value (excluding surrogates)
 */
function generateUnicodeScalar(rng: RNG): number {
  // Valid Unicode scalar values are:
  // Range 1: 0x0000-0xD7FF (55296 values: 0x0000 to 0xD7FF inclusive)
  // Range 2: 0xE000-0xFFFF (8192 values: 0xE000 to 0xFFFF inclusive)
  // Range 3: 0x10000-0x10FFFF (1048576 values: 0x10000 to 0x10FFFF inclusive)
  // Total: 1112064 valid scalar values
  
  const random = rng.random();
  const totalValid = 1112064;
  const range1Size = 55296;  // 0x0000 to 0xD7FF
  const range2Size = 8192;   // 0xE000 to 0xFFFF
  
  const position = Math.floor(random * totalValid);
  
  if (position < range1Size) {
    // Range 0x0000-0xD7FF
    return position;
  } else if (position < range1Size + range2Size) {
    // Range 0xE000-0xFFFF
    return 0xE000 + (position - range1Size);
  } else {
    // Range 0x10000-0x10FFFF
    const offset = position - range1Size - range2Size;
    return 0x10000 + offset;
  }
}

/**
 * Converts a Unicode scalar value to a JavaScript string
 * JavaScript strings are UTF-16, but String.fromCodePoint handles all valid scalars correctly
 */
function scalarToString(scalar: number): string {
  return String.fromCodePoint(scalar);
}

/**
 * Strategy for generating values from a String domain
 */
export class StringDomainGenerator implements DomainGeneratorStrategy<string> {
  generate(domain: Domain<string>, rng: RNG): string {
    const stringDomain = domain as CompoundStringDomain;
    
    // Check if this is a compound string with parts
    if (stringDomain._parts) {
      return this.generateCompoundString(stringDomain._parts, rng);
    }
    
    // Charset domain
    if (domain instanceof CharSetDomain) {
      return this.generateFromCharSet(domain, rng);
    }
    
    // Default: generate random Unicode string
    return this.generateUnicodeString(stringDomain, rng);
  }

  /**
   * Generate from a compound string with parts
   */
  private generateCompoundString(parts: StringPart[], rng: RNG): string {
    return parts.map(part => {
      if (typeof part === 'string') {
        return part;
      }
      // Generate from the part domain (skip validators - only domains are stored)
      return this.generate(part as StringDomain, rng);
    }).join('');
  }

  /**
   * Generate from a character set defined by ranges.
   * 
   * Picks a random character proportionally from all ranges:
   * 1. Compute total size of all ranges
   * 2. Pick a random index in [0, totalSize)
   * 3. Map that index to a specific range and offset
   */
  private generateFromCharSet(domain: CharSetDomain, rng: RNG): string {
    const { ranges, size, minLength, maxLength } = domain;
    
    if (size === 0) {
      return ''; // Empty charset
    }
    
    const length = minLength + Math.floor(rng.random() * (maxLength - minLength + 1));
    
    let result = '';
    for (let i = 0; i < length; i++) {
      // Pick a random position in the total character space
      const pos = Math.floor(rng.random() * size);
      
      // Find which range this position falls into
      let remaining = pos;
      for (const range of ranges) {
        const rangeSize = range.max - range.min + 1;
        if (remaining < rangeSize) {
          // This position is within this range
          const codePoint = range.min + remaining;
          result += String.fromCodePoint(codePoint);
          break;
        }
        remaining -= rangeSize;
      }
    }
    return result;
  }

  /**
   * Generate a random Unicode string
   */
  private generateUnicodeString(stringDomain: StringDomain, rng: RNG): string {
    const minLength = stringDomain.minLength ?? 0;
    const maxLength = stringDomain.maxLength ?? 100;
    
    // Generate a random target length (in JavaScript string length = UTF-16 code units)
    const targetLength = minLength + Math.floor(rng.random() * (maxLength - minLength + 1));
    
    // Generate a string of that length
    // Note: JavaScript string.length counts UTF-16 code units
    // A Unicode scalar value can be 1 or 2 code units (surrogate pair for values > 0xFFFF)
    let result = '';
    
    while (result.length < targetLength) {
      const scalar = generateUnicodeScalar(rng);
      const char = scalarToString(scalar);
      
      // Check if adding this character would exceed maxLength
      if (stringDomain.maxLength !== undefined && result.length + char.length > stringDomain.maxLength) {
        break;
      }
      
      result += char;
    }
    
    // Ensure minimum length is met
    while (stringDomain.minLength !== undefined && result.length < stringDomain.minLength) {
      const scalar = generateUnicodeScalar(rng);
      const char = scalarToString(scalar);
      result += char;
      
      // Safety check to avoid infinite loop
      if (result.length > (stringDomain.maxLength ?? 1000)) {
        break;
      }
    }
    
    return result;
  }
}

