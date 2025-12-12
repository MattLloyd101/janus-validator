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
export function parseRegexToAST(source: string): RegexASTNode {
  const parser = new RegexASTParserImpl(source);
  return parser.parse();
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
    const chars: string[] = [];

    while (!this.isEnd() && this.peek() !== ']') {
      const expandedChars = this.parseCharClassChars();

      // Check for range
      if (
        expandedChars.length === 1 &&
        !this.isEnd() &&
        this.peek() === '-' &&
        this.source[this.pos + 1] !== ']'
      ) {
        this.consume(); // '-'
        const endChars = this.parseCharClassChars();
        if (endChars.length !== 1) {
          throw new Error(`Cannot use character class escape as range endpoint at position ${this.pos}`);
        }
        for (let c = expandedChars[0].charCodeAt(0); c <= endChars[0].charCodeAt(0); c++) {
          chars.push(String.fromCharCode(c));
        }
      } else {
        chars.push(...expandedChars);
      }
    }

    if (!this.match(']')) {
      throw new Error(`Expected ']' at position ${this.pos}`);
    }

    return { type: RegexNodeType.CHAR_CLASS, chars, negated };
  }

  private parseCharClassChars(): string[] {
    if (this.peek() === '\\') {
      this.consume();
      return this.parseCharClassEscape();
    }
    return [this.consume()];
  }

  private parseCharClassEscape(): string[] {
    const ch = this.peek();

    if (ch === 'd') {
      this.consume();
      return ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'];
    }
    if (ch === 'D') {
      this.consume();
      const chars: string[] = [];
      for (let c = 32; c <= 126; c++) {
        if (c < 48 || c > 57) {
          chars.push(String.fromCharCode(c));
        }
      }
      return chars;
    }
    if (ch === 'w') {
      this.consume();
      const chars: string[] = [];
      for (let c = 'a'.charCodeAt(0); c <= 'z'.charCodeAt(0); c++) {
        chars.push(String.fromCharCode(c));
      }
      for (let c = 'A'.charCodeAt(0); c <= 'Z'.charCodeAt(0); c++) {
        chars.push(String.fromCharCode(c));
      }
      for (let c = '0'.charCodeAt(0); c <= '9'.charCodeAt(0); c++) {
        chars.push(String.fromCharCode(c));
      }
      chars.push('_');
      return chars;
    }
    if (ch === 'W') {
      this.consume();
      const wordChars = new Set<number>();
      for (let c = 'a'.charCodeAt(0); c <= 'z'.charCodeAt(0); c++) wordChars.add(c);
      for (let c = 'A'.charCodeAt(0); c <= 'Z'.charCodeAt(0); c++) wordChars.add(c);
      for (let c = '0'.charCodeAt(0); c <= '9'.charCodeAt(0); c++) wordChars.add(c);
      wordChars.add('_'.charCodeAt(0));

      const chars: string[] = [];
      for (let c = 32; c <= 126; c++) {
        if (!wordChars.has(c)) {
          chars.push(String.fromCharCode(c));
        }
      }
      return chars;
    }
    if (ch === 's') {
      this.consume();
      return [' ', '\t', '\n', '\r', '\f', '\v'];
    }
    if (ch === 'S') {
      this.consume();
      const whitespace = new Set([' ', '\t', '\n', '\r', '\f', '\v']);
      const chars: string[] = [];
      for (let c = 32; c <= 126; c++) {
        const char = String.fromCharCode(c);
        if (!whitespace.has(char)) {
          chars.push(char);
        }
      }
      return chars;
    }

    return [this.parseEscapeChar()];
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

    // Character class escapes
    if (ch === 'd') {
      this.consume();
      return { type: RegexNodeType.CHAR_CLASS, chars: ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'], negated: false } as CharClassNode;
    }
    if (ch === 'D') {
      this.consume();
      return { type: RegexNodeType.CHAR_CLASS, chars: ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'], negated: true } as CharClassNode;
    }
    if (ch === 'w') {
      this.consume();
      const chars: string[] = [];
      for (let c = 'a'.charCodeAt(0); c <= 'z'.charCodeAt(0); c++) chars.push(String.fromCharCode(c));
      for (let c = 'A'.charCodeAt(0); c <= 'Z'.charCodeAt(0); c++) chars.push(String.fromCharCode(c));
      for (let c = '0'.charCodeAt(0); c <= '9'.charCodeAt(0); c++) chars.push(String.fromCharCode(c));
      chars.push('_');
      return { type: RegexNodeType.CHAR_CLASS, chars, negated: false } as CharClassNode;
    }
    if (ch === 'W') {
      this.consume();
      const chars: string[] = [];
      for (let c = 'a'.charCodeAt(0); c <= 'z'.charCodeAt(0); c++) chars.push(String.fromCharCode(c));
      for (let c = 'A'.charCodeAt(0); c <= 'Z'.charCodeAt(0); c++) chars.push(String.fromCharCode(c));
      for (let c = '0'.charCodeAt(0); c <= '9'.charCodeAt(0); c++) chars.push(String.fromCharCode(c));
      chars.push('_');
      return { type: RegexNodeType.CHAR_CLASS, chars, negated: true } as CharClassNode;
    }
    if (ch === 's') {
      this.consume();
      return { type: RegexNodeType.CHAR_CLASS, chars: [' ', '\t', '\n', '\r', '\f', '\v'], negated: false } as CharClassNode;
    }
    if (ch === 'S') {
      this.consume();
      return { type: RegexNodeType.CHAR_CLASS, chars: [' ', '\t', '\n', '\r', '\f', '\v'], negated: true } as CharClassNode;
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

