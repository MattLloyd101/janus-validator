import {
  RegexNodeType,
  AnchorKind,
  RegexASTNode,
  LiteralNode,
  CharClassNode,
  AnyNode,
  AnchorNode,
  EmptyNode,
  SequenceNode,
  AlternationNode,
  QuantifierNode,
  GroupNode,
} from './RegexAST';
import type { CharRange } from '../Domain';

/**
 * Parser that converts a regex source string into an AST.
 * 
 * This parser handles the PORTABLE SUBSET of regex:
 * - Literals and escape sequences (\n, \t, \r, etc.)
 * - Character classes (including negated and ranges): [abc], [a-z], [^0-9]
 * - Quantifiers (*, +, ?, {n}, {n,}, {n,m})
 * - Groups (capturing and non-capturing)
 * - Alternation (|)
 * - Anchors (^, $)
 * - Any character (.)
 * 
 * NON-PORTABLE constructs are REJECTED (see ADR-002):
 * - Character class escapes (\d, \w, \s, \D, \W, \S) - use explicit [0-9], [A-Za-z0-9_], [ \t\r\n] instead
 * - Word boundaries (\b, \B) - not portable across engines
 * - Lookaheads/lookbehinds (?=...), (?!...), (?<=...), (?<!...)
 * - Backreferences (\1, \k<name>)
 * - Flags (i, g, m, s, etc.)
 * 
 * @example
 * ```typescript
 * const ast = parseRegexToAST('[a-z]+@[a-z]+\\.[a-z]{2,3}');
 * // Returns an AST representing the email-like pattern
 * ```
 */
export function parseRegexToAST(source: string, flags: string = ''): RegexASTNode {
  assertSupportedPortableRegex(source, flags);
  const parser = new RegexASTParserImpl(source);
  return parser.parse();
}

/**
 * Validate that the regex source is within the supported (portable/decidable) subset.
 *
 * IMPORTANT:
 * - This is intentionally a *parser-level* responsibility (not `Domain.encapsulates()`),
 *   because unsupported constructs should fail fast with explicit errors.
 * - This is NOT trying to accept "all regex"; it rejects constructs we don't model
 *   correctly (e.g. lookarounds/backrefs), even if some engines would treat them specially.
 */
function assertSupportedPortableRegex(source: string, flags: string): void {
  const src = source ?? '';

  if (flags && flags.length > 0) {
    throw new Error(`Unsupported regex flags: "${flags}"`);
  }

  // Disallow lookarounds and inline-flag groups.
  // These start with "(?" but are NOT "(?:", which is allowed.
  // Examples to reject: (?=...), (?!...), (?<=...), (?<!...), (?i:...), (?i)
  for (let i = 0; i < src.length - 1; i++) {
    if (src[i] !== '(' || src[i + 1] !== '?') continue;
    const third = src[i + 2] ?? '';
    const fourth = src[i + 3] ?? '';
    const isNonCapturing = third === ':'; // (?:...)
    if (isNonCapturing) continue;
    const token = `(?${third}${fourth}`;
    throw new Error(`Unsupported regex construct: ${token}...`);
  }

  // Disallow backreferences like \1, \2, ... and \k<name>.
  // NOTE: Without this, the parser would incorrectly treat them as literals.
  if (/\\[1-9][0-9]*/.test(src)) {
    throw new Error('Unsupported regex construct: numeric backreference (e.g. \\1)');
  }
  if (/\\k<[^>]+>/.test(src)) {
    throw new Error('Unsupported regex construct: named backreference (e.g. \\k<name>)');
  }

  // Disallow non-portable character class escapes.
  // These have inconsistent behavior across regex engines (especially for Unicode).
  // Use explicit character classes instead:
  //   \d -> [0-9]
  //   \w -> [A-Za-z0-9_]
  //   \s -> [ \t\r\n]
  //   \b -> (word boundary - not portable)
  const nonPortableEscapes = [
    { escape: '\\d', replacement: '[0-9]' },
    { escape: '\\D', replacement: '[^0-9]' },
    { escape: '\\w', replacement: '[A-Za-z0-9_]' },
    { escape: '\\W', replacement: '[^A-Za-z0-9_]' },
    { escape: '\\s', replacement: '[ \\t\\r\\n]' },
    { escape: '\\S', replacement: '[^ \\t\\r\\n]' },
    { escape: '\\b', replacement: '(word boundary anchor)' },
    { escape: '\\B', replacement: '(non-word boundary anchor)' },
  ];

  for (const { escape, replacement } of nonPortableEscapes) {
    // Check for the escape sequence (need to handle both raw and escaped forms)
    const escapePattern = escape.replace('\\', '\\\\');
    if (new RegExp(escapePattern).test(src)) {
      throw new Error(
        `Unsupported regex escape: ${escape} is not portable across engines. ` +
        `Use explicit ${replacement} instead.`
      );
    }
  }
}

/**
 * Internal parser implementation
 */
class RegexASTParserImpl {
  private pos = 0;

  constructor(private source: string) {}

  parse(): RegexASTNode {
    return this.parseAlternation();
  }

  private isEnd(): boolean {
    return this.pos >= this.source.length;
  }

  private peek(): string {
    return this.source[this.pos];
  }

  private consume(): string {
    return this.source[this.pos++];
  }

  private match(expected: string): boolean {
    if (this.peek() === expected) {
      this.pos++;
      return true;
    }
    return false;
  }

  private parseAlternation(): RegexASTNode {
    const options: RegexASTNode[] = [];
    options.push(this.parseSequence());

    while (!this.isEnd() && this.match('|')) {
      options.push(this.parseSequence());
    }

    if (options.length === 1) {
      return options[0];
    }
    return { type: RegexNodeType.ALTERNATION, options } as AlternationNode;
  }

  private parseSequence(): RegexASTNode {
    const nodes: RegexASTNode[] = [];

    while (!this.isEnd() && !this.isSequenceTerminator()) {
      nodes.push(this.parseQuantified());
    }

    if (nodes.length === 0) {
      return { type: RegexNodeType.EMPTY } as EmptyNode;
    }
    if (nodes.length === 1) {
      return nodes[0];
    }
    return { type: RegexNodeType.SEQUENCE, nodes } as SequenceNode;
  }

  private isSequenceTerminator(): boolean {
    const ch = this.peek();
    return ch === '|' || ch === ')';
  }

  private parseQuantified(): RegexASTNode {
    const node = this.parseTerm();

    if (this.isEnd()) return node;

    const ch = this.peek();

    if (ch === '*') {
      this.consume();
      return { type: RegexNodeType.QUANTIFIER, node, min: 0, max: Infinity } as QuantifierNode;
    }
    if (ch === '+') {
      this.consume();
      return { type: RegexNodeType.QUANTIFIER, node, min: 1, max: Infinity } as QuantifierNode;
    }
    if (ch === '?') {
      this.consume();
      return { type: RegexNodeType.QUANTIFIER, node, min: 0, max: 1 } as QuantifierNode;
    }
    if (ch === '{') {
      return this.parseRepetition(node);
    }

    return node;
  }

  private parseRepetition(node: RegexASTNode): QuantifierNode {
    this.consume(); // '{'

    let min = this.parseNumber();
    let max = min;

    if (this.match(',')) {
      if (this.peek() === '}') {
        max = Infinity;
      } else {
        max = this.parseNumber();
      }
    }

    if (!this.match('}')) {
      throw new Error(`Expected '}' at position ${this.pos}`);
    }

    return { type: RegexNodeType.QUANTIFIER, node, min, max };
  }

  private parseNumber(): number {
    let num = '';
    while (!this.isEnd() && this.peek() >= '0' && this.peek() <= '9') {
      num += this.consume();
    }
    if (num.length === 0) {
      throw new Error(`Expected number at position ${this.pos}`);
    }
    return parseInt(num, 10);
  }

  private parseTerm(): RegexASTNode {
    if (this.isEnd()) {
      return { type: RegexNodeType.EMPTY } as EmptyNode;
    }

    const ch = this.peek();

    // Anchors
    if (ch === '^') {
      this.consume();
      return { type: RegexNodeType.ANCHOR, kind: AnchorKind.START } as AnchorNode;
    }
    if (ch === '$') {
      this.consume();
      return { type: RegexNodeType.ANCHOR, kind: AnchorKind.END } as AnchorNode;
    }

    // Any character
    if (ch === '.') {
      this.consume();
      return { type: RegexNodeType.ANY } as AnyNode;
    }

    // Character class
    if (ch === '[') {
      return this.parseCharClass();
    }

    // Group
    if (ch === '(') {
      return this.parseGroup();
    }

    // Escape sequence
    if (ch === '\\') {
      return this.parseEscape();
    }

    // Literal character
    this.consume();
    return { type: RegexNodeType.LITERAL, char: ch } as LiteralNode;
  }

  private parseCharClass(): CharClassNode {
    this.consume(); // '['

    const negated = this.match('^');
    const ranges: CharRange[] = [];

    while (!this.isEnd() && this.peek() !== ']') {
      const item = this.parseCharClassItem();

      // Check for range (only if item is a single character)
      if (
        item.type === 'char' &&
        !this.isEnd() &&
        this.peek() === '-' &&
        this.source[this.pos + 1] !== ']'
      ) {
        this.consume(); // '-'
        const endItem = this.parseCharClassItem();
        if (endItem.type !== 'char') {
          throw new Error(`Cannot use character class escape as range endpoint at position ${this.pos}`);
        }
        ranges.push({ min: item.codePoint, max: endItem.codePoint });
      } else if (item.type === 'char') {
        ranges.push({ min: item.codePoint, max: item.codePoint });
      } else {
        // Multiple ranges from escape like \d, \w
        ranges.push(...item.ranges);
      }
    }

    if (!this.match(']')) {
      throw new Error(`Expected ']' at position ${this.pos}`);
    }

    return { type: RegexNodeType.CHAR_CLASS, ranges: this.normalizeRanges(ranges), negated };
  }

  /**
   * Result of parsing a char class item - either a single char or multiple ranges
   */
  private parseCharClassItem(): { type: 'char'; codePoint: number } | { type: 'ranges'; ranges: CharRange[] } {
    if (this.peek() === '\\') {
      this.consume();
      return this.parseCharClassEscape();
    }
    const ch = this.consume();
    return { type: 'char', codePoint: ch.codePointAt(0)! };
  }

  private parseCharClassEscape(): { type: 'char'; codePoint: number } | { type: 'ranges'; ranges: CharRange[] } {
    // Note: Non-portable escapes (\d, \D, \w, \W, \s, \S, \b, \B) are rejected
    // by assertSupportedPortableRegex before parsing. This method only handles
    // simple escape sequences that are portable (like \n, \t, \\, etc.)
    const escaped = this.parseEscapeChar();
    return { type: 'char', codePoint: escaped.codePointAt(0)! };
  }

  /**
   * Normalizes ranges by sorting and merging overlapping/adjacent ranges.
   */
  private normalizeRanges(ranges: CharRange[]): CharRange[] {
    if (ranges.length === 0) return [];
    
    const sorted = [...ranges].sort((a, b) => a.min - b.min || b.max - a.max);
    const result: CharRange[] = [];
    let current = { ...sorted[0] };
    
    for (let i = 1; i < sorted.length; i++) {
      const next = sorted[i];
      if (next.min <= current.max + 1) {
        current.max = Math.max(current.max, next.max);
      } else {
        result.push(current);
        current = { ...next };
      }
    }
    result.push(current);
    
    return result;
  }

  private parseGroup(): GroupNode {
    this.consume(); // '('

    let capturing = true;

    // Check for non-capturing group (?:...)
    if (this.peek() === '?' && this.source[this.pos + 1] === ':') {
      this.consume(); // '?'
      this.consume(); // ':'
      capturing = false;
    }

    const inner = this.parseAlternation();

    if (!this.match(')')) {
      throw new Error(`Expected ')' at position ${this.pos}`);
    }

    return { type: RegexNodeType.GROUP, node: inner, capturing };
  }

  private parseEscape(): RegexASTNode {
    this.consume(); // '\'

    if (this.isEnd()) {
      throw new Error('Unexpected end of pattern after escape');
    }

    // Note: Non-portable escapes (\d, \D, \w, \W, \s, \S, \b, \B) are rejected
    // by assertSupportedPortableRegex before parsing. This method only handles
    // simple escape sequences that are portable (like \n, \t, \\, etc.)
    const escaped = this.parseEscapeChar();
    return { type: RegexNodeType.LITERAL, char: escaped } as LiteralNode;
  }

  private parseEscapeChar(): string {
    const ch = this.consume();

    switch (ch) {
      case 'n': return '\n';
      case 'r': return '\r';
      case 't': return '\t';
      case 'f': return '\f';
      case 'v': return '\v';
      case '0': return '\0';
      default: return ch;
    }
  }
}

