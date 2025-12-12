import { Domain, RegexDomain } from '../Domain';
import { RNG } from '../RNG';
import { DomainGeneratorStrategy } from './DomainGeneratorStrategy';
import { parseRegexToAST, RegexASTNode, RegexNodeType } from '../regex';

/**
 * Default maximum repetitions for unbounded quantifiers (*, +)
 */
const DEFAULT_MAX_UNBOUNDED = 10;

/**
 * Printable ASCII characters for 'any' character (.) and negated classes
 */
const PRINTABLE_ASCII: string[] = [];
for (let c = 32; c <= 126; c++) {
  PRINTABLE_ASCII.push(String.fromCharCode(c));
}

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
 * const domain: RegexDomain = { type: DomainType.REGEX_DOMAIN, pattern: /\d{3}/, source: '\\d{3}' };
 * const value = generator.generate(domain, rng); // e.g., "472"
 * ```
 */
export class RegexDomainGenerator implements DomainGeneratorStrategy<string> {
  /**
   * Generate a string that matches the regex pattern in the domain
   */
  generate(domain: Domain<string>, rng: RNG): string {
    const regexDomain = domain as RegexDomain;
    const ast = parseRegexToAST(regexDomain.source);
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
        return this.generateCharClass(node.chars, node.negated, rng);

      case RegexNodeType.ANY:
        return PRINTABLE_ASCII[Math.floor(rng.random() * PRINTABLE_ASCII.length)];

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
   * Generate a character from a character class
   */
  private generateCharClass(chars: string[], negated: boolean, rng: RNG): string {
    if (negated) {
      const available = PRINTABLE_ASCII.filter(c => !chars.includes(c));
      if (available.length === 0) {
        throw new Error('Negated character class excludes all printable ASCII characters');
      }
      return available[Math.floor(rng.random() * available.length)];
    } else {
      if (chars.length === 0) {
        throw new Error('Empty character class');
      }
      return chars[Math.floor(rng.random() * chars.length)];
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
