import { Domain, RegexDomain, CharRange } from '../Domain';
import { RNG } from '../RNG';
import { DomainGeneratorStrategy } from './DomainGeneratorStrategy';
import { parseRegexToAST, RegexASTNode, RegexNodeType } from '../regex';

/**
 * Default maximum repetitions for unbounded quantifiers (*, +)
 */
const DEFAULT_MAX_UNBOUNDED = 10;

/**
 * Printable ASCII range for 'any' character (.) and negated classes
 */
const PRINTABLE_ASCII_MIN = 32;  // space
const PRINTABLE_ASCII_MAX = 126; // ~
const PRINTABLE_ASCII_SIZE = PRINTABLE_ASCII_MAX - PRINTABLE_ASCII_MIN + 1;

/**
 * Strategy for generating strings that match a regular expression pattern.
 * 
 * This implementation:
 * 1. Parses the regex source into an AST using RegexASTParser
 * 2. Traverses the AST to generate matching strings
 * 
 * The generator produces valid strings that would match the original regex.
 * 
 * @example
 * ```typescript
 * const generator = new RegexDomainGenerator();
 * const domain = new RegexDomain(/[0-9]{3}/); // Use [0-9] instead of \d
 * const value = generator.generate(domain, rng); // e.g., "472"
 * ```
 */
export class RegexDomainGenerator implements DomainGeneratorStrategy<string> {
  /**
   * Generate a string that matches the regex pattern in the domain
   */
  generate(domain: Domain<string>, rng: RNG): string {
    const regexDomain = domain as RegexDomain;
    const ast = parseRegexToAST(regexDomain.source, regexDomain.pattern?.flags ?? '');
    return this.generateFromAST(ast, rng);
  }

  /**
   * Generate a string by traversing the AST
   */
  private generateFromAST(node: RegexASTNode, rng: RNG): string {
    switch (node.type) {
      case RegexNodeType.LITERAL:
        return node.char;

      case RegexNodeType.CHAR_CLASS:
        return this.generateCharClass(node.ranges, node.negated, rng);

      case RegexNodeType.ANY:
        // Generate any printable ASCII character
        const codePoint = PRINTABLE_ASCII_MIN + Math.floor(rng.random() * PRINTABLE_ASCII_SIZE);
        return String.fromCodePoint(codePoint);

      case RegexNodeType.ANCHOR:
      case RegexNodeType.EMPTY:
        return '';

      case RegexNodeType.SEQUENCE:
        return node.nodes.map(n => this.generateFromAST(n, rng)).join('');

      case RegexNodeType.ALTERNATION:
        if (node.options.length === 0) return '';
        const optIndex = Math.floor(rng.random() * node.options.length);
        return this.generateFromAST(node.options[optIndex], rng);

      case RegexNodeType.QUANTIFIER:
        return this.generateQuantifier(node.node, node.min, node.max, rng);

      case RegexNodeType.GROUP:
        return this.generateFromAST(node.node, rng);
    }
  }

  /**
   * Generate a character from a character class defined by ranges.
   */
  private generateCharClass(ranges: readonly CharRange[], negated: boolean, rng: RNG): string {
    if (negated) {
      // For negated classes, generate from printable ASCII minus the excluded ranges
      const excludedRanges = ranges;
      
      // Build list of available code points in printable ASCII
      const available: number[] = [];
      for (let cp = PRINTABLE_ASCII_MIN; cp <= PRINTABLE_ASCII_MAX; cp++) {
        const isExcluded = excludedRanges.some(r => cp >= r.min && cp <= r.max);
        if (!isExcluded) {
          available.push(cp);
        }
      }
      
      if (available.length === 0) {
        throw new Error('Negated character class excludes all printable ASCII characters');
      }
      
      const idx = Math.floor(rng.random() * available.length);
      return String.fromCodePoint(available[idx]);
    } else {
      // Calculate total size of all ranges
      const totalSize = ranges.reduce((sum, r) => sum + (r.max - r.min + 1), 0);
      
      if (totalSize === 0) {
        throw new Error('Empty character class');
      }
      
      // Pick a random position in the total character space
      const pos = Math.floor(rng.random() * totalSize);
      
      // Find which range this position falls into
      let remaining = pos;
      for (const range of ranges) {
        const rangeSize = range.max - range.min + 1;
        if (remaining < rangeSize) {
          return String.fromCodePoint(range.min + remaining);
        }
        remaining -= rangeSize;
      }
      
      // Fallback (shouldn't reach here)
      return String.fromCodePoint(ranges[0].min);
    }
  }

  /**
   * Generate a repeated pattern based on quantifier bounds
   */
  private generateQuantifier(node: RegexASTNode, min: number, max: number, rng: RNG): string {
    const effectiveMax = max === Infinity ? DEFAULT_MAX_UNBOUNDED : max;
    const range = effectiveMax - min + 1;
    const count = min + Math.floor(rng.random() * range);

    let result = '';
    for (let i = 0; i < count; i++) {
      result += this.generateFromAST(node, rng);
    }
    return result;
  }
}
