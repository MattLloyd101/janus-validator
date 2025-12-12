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

// ============================================================================
// Predefined character class ranges
// ============================================================================

/** Range for digits 0-9 */
const DIGIT_RANGE: CharRange = { min: 0x30, max: 0x39 };

/** Ranges for word characters [a-zA-Z0-9_] */
const WORD_RANGES: readonly CharRange[] = [
  { min: 0x30, max: 0x39 }, // 0-9
  { min: 0x41, max: 0x5A }, // A-Z
  { min: 0x5F, max: 0x5F }, // _
  { min: 0x61, max: 0x7A }, // a-z
];

/** Ranges for whitespace [ \t\n\v\f\r] */
const WHITESPACE_RANGES: readonly CharRange[] = [
  { min: 0x09, max: 0x0D }, // \t \n \v \f \r (contiguous)
  { min: 0x20, max: 0x20 }, // space
];

/**
 * Parser that converts a regex source string into an AST.
 * 
 * This parser handles:
 * - Literals and escape sequences
 * - Character classes (including negated and ranges)
 * - Character class escapes (\d, \w, \s and their negations)
 * - Quantifiers (*, +, ?, {n}, {n,}, {n,m})
 * - Groups (capturing and non-capturing)
 * - Alternation (|)
 * - Anchors (^, $, \b)
 * - Any character (.)
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
    const ch = this.peek();

    if (ch === 'd') {
      this.consume();
      return { type: 'ranges', ranges: [DIGIT_RANGE] };
    }
    if (ch === 'D') {
      this.consume();
      // Non-digits in ASCII printable range: complement of 0-9
      // For simplicity, we use printable ASCII minus digits
      return { type: 'ranges', ranges: [{ min: 0x20, max: 0x2F }, { min: 0x3A, max: 0x7E }] };
    }
    if (ch === 'w') {
      this.consume();
      return { type: 'ranges', ranges: [...WORD_RANGES] };
    }
    if (ch === 'W') {
      this.consume();
      // Non-word in ASCII printable: complement of [0-9A-Z_a-z]
      return { type: 'ranges', ranges: [
        { min: 0x20, max: 0x2F }, // space to /
        { min: 0x3A, max: 0x40 }, // : to @
        { min: 0x5B, max: 0x5E }, // [ to ^
        { min: 0x60, max: 0x60 }, // `
        { min: 0x7B, max: 0x7E }, // { to ~
      ]};
    }
    if (ch === 's') {
      this.consume();
      return { type: 'ranges', ranges: [...WHITESPACE_RANGES] };
    }
    if (ch === 'S') {
      this.consume();
      // Non-whitespace in ASCII printable: complement of [ \t\n\v\f\r]
      return { type: 'ranges', ranges: [
        { min: 0x21, max: 0x7E }, // ! to ~ (excludes space)
      ]};
    }

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

    const ch = this.peek();

    // Explicitly reject unsupported escapes that are meaningful in regex engines
    // but not represented in our AST.
    if (ch === 'B') {
      throw new Error('Unsupported regex escape: \\B');
    }

    // Character class escapes
    if (ch === 'd') {
      this.consume();
      return { type: RegexNodeType.CHAR_CLASS, ranges: [DIGIT_RANGE], negated: false } as CharClassNode;
    }
    if (ch === 'D') {
      this.consume();
      return { type: RegexNodeType.CHAR_CLASS, ranges: [DIGIT_RANGE], negated: true } as CharClassNode;
    }
    if (ch === 'w') {
      this.consume();
      return { type: RegexNodeType.CHAR_CLASS, ranges: [...WORD_RANGES], negated: false } as CharClassNode;
    }
    if (ch === 'W') {
      this.consume();
      return { type: RegexNodeType.CHAR_CLASS, ranges: [...WORD_RANGES], negated: true } as CharClassNode;
    }
    if (ch === 's') {
      this.consume();
      return { type: RegexNodeType.CHAR_CLASS, ranges: [...WHITESPACE_RANGES], negated: false } as CharClassNode;
    }
    if (ch === 'S') {
      this.consume();
      return { type: RegexNodeType.CHAR_CLASS, ranges: [...WHITESPACE_RANGES], negated: true } as CharClassNode;
    }

    // Word boundary - generates nothing
    if (ch === 'b') {
      this.consume();
      return { type: RegexNodeType.ANCHOR, kind: AnchorKind.WORD_BOUNDARY } as AnchorNode;
    }

    // Literal escape
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

