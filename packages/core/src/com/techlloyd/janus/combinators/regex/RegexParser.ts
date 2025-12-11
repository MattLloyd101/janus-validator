import { RegexValidator } from './RegexValidator';
import { Literal } from './Literal';
import { CharClass, CharClasses } from './CharClass';
import { Any } from './Any';
import { Empty } from './Empty';
import { Anchor } from './Anchor';
import { RegexSequence } from './Sequence';
import { RegexAlternation } from './Alternation';
import { Quantifier } from './Quantifier';
import { Group } from './Group';

/**
 * Parser that converts a regex pattern string into a composed RegexValidator
 * 
 * Uses recursive descent parsing to handle:
 * - Literals and escaped characters
 * - Character classes: [abc], [a-z], [^abc]
 * - Quantifiers: *, +, ?, {n}, {n,}, {n,m}
 * - Groups: (abc), (?:abc)
 * - Alternation: a|b
 * - Anchors: ^, $
 * - Any character: .
 * - Common escape sequences: \d, \w, \s, etc.
 */
export class RegexParser {
  private source: string;
  private pos: number;

  constructor(source: string) {
    this.source = source;
    this.pos = 0;
  }

  /**
   * Parse the regex pattern and return a composed RegexValidator
   */
  parse(): RegexValidator {
    const result = this.parseAlternation();
    if (this.pos < this.source.length) {
      throw new Error(`Unexpected character at position ${this.pos}: '${this.source[this.pos]}'`);
    }
    return result;
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

  /**
   * Parse alternation: a|b|c
   */
  private parseAlternation(): RegexValidator {
    const options: RegexValidator[] = [];
    options.push(this.parseSequence());

    while (!this.isEnd() && this.match('|')) {
      options.push(this.parseSequence());
    }

    return RegexAlternation.create(...options);
  }

  /**
   * Parse a sequence of terms
   */
  private parseSequence(): RegexValidator {
    const validators: RegexValidator[] = [];

    while (!this.isEnd() && !this.isSequenceTerminator()) {
      validators.push(this.parseQuantified());
    }

    return RegexSequence.create(...validators);
  }

  private isSequenceTerminator(): boolean {
    const ch = this.peek();
    return ch === '|' || ch === ')';
  }

  /**
   * Parse a term with optional quantifier
   */
  private parseQuantified(): RegexValidator {
    const validator = this.parseTerm();

    if (this.isEnd()) return validator;

    const ch = this.peek();

    if (ch === '*') {
      this.consume();
      return Quantifier.zeroOrMore(validator);
    }
    if (ch === '+') {
      this.consume();
      return Quantifier.oneOrMore(validator);
    }
    if (ch === '?') {
      this.consume();
      return Quantifier.optional(validator);
    }
    if (ch === '{') {
      return this.parseRepetition(validator);
    }

    return validator;
  }

  /**
   * Parse {n}, {n,}, or {n,m} repetition
   */
  private parseRepetition(validator: RegexValidator): RegexValidator {
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

    return new Quantifier(validator, min, max);
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

  /**
   * Parse a single term (atom)
   */
  private parseTerm(): RegexValidator {
    if (this.isEnd()) {
      return new Empty();
    }

    const ch = this.peek();

    // Anchors
    if (ch === '^') {
      this.consume();
      return new Anchor('start');
    }
    if (ch === '$') {
      this.consume();
      return new Anchor('end');
    }

    // Any character
    if (ch === '.') {
      this.consume();
      return new Any();
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
    return new Literal(ch);
  }

  /**
   * Parse a character class: [abc], [a-z], [^abc]
   * Handles shorthand escapes (\d, \s, \w) by expanding them.
   */
  private parseCharClass(): RegexValidator {
    this.consume(); // '['

    const negated = this.match('^');
    const chars: string[] = [];

    while (!this.isEnd() && this.peek() !== ']') {
      const expandedChars = this.parseCharClassChars();

      // Check for range (only valid for single-character results)
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
        // Expand range
        for (let c = expandedChars[0].charCodeAt(0); c <= endChars[0].charCodeAt(0); c++) {
          chars.push(String.fromCharCode(c));
        }
      } else {
        // Add all expanded characters
        chars.push(...expandedChars);
      }
    }

    if (!this.match(']')) {
      throw new Error(`Expected ']' at position ${this.pos}`);
    }

    return new CharClass(chars, negated);
  }

  /**
   * Parse a character (or expanded character set) inside a character class.
   * Returns an array of characters to support expanding \d, \s, \w inside [...].
   */
  private parseCharClassChars(): string[] {
    if (this.peek() === '\\') {
      this.consume();
      return this.parseCharClassEscape();
    }
    return [this.consume()];
  }

  /**
   * Parse an escape sequence inside a character class.
   * Expands shorthand classes (\d, \s, \w) to their character arrays.
   */
  private parseCharClassEscape(): string[] {
    const ch = this.peek();

    // Shorthand character class escapes - expand to character arrays
    if (ch === 'd') {
      this.consume();
      return ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'];
    }
    if (ch === 'D') {
      this.consume();
      // Non-digit: all printable ASCII except digits
      const chars: string[] = [];
      for (let c = 32; c <= 126; c++) {
        if (c < 48 || c > 57) { // not 0-9
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
      // Non-word: all printable ASCII except word chars
      const wordChars = new Set<number>();
      for (let c = 'a'.charCodeAt(0); c <= 'z'.charCodeAt(0); c++) {
        wordChars.add(c);
      }
      for (let c = 'A'.charCodeAt(0); c <= 'Z'.charCodeAt(0); c++) {
        wordChars.add(c);
      }
      for (let c = '0'.charCodeAt(0); c <= '9'.charCodeAt(0); c++) {
        wordChars.add(c);
      }
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
      // Non-whitespace: all printable ASCII except whitespace
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

    // Regular escape character
    return [this.parseEscapeChar()];
  }

  /**
   * Parse a group: (abc), (?:abc)
   */
  private parseGroup(): RegexValidator {
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

    return new Group(inner, capturing);
  }

  /**
   * Parse an escape sequence
   */
  private parseEscape(): RegexValidator {
    this.consume(); // '\'

    if (this.isEnd()) {
      throw new Error('Unexpected end of pattern after escape');
    }

    const ch = this.peek();

    // Character class escapes
    if (ch === 'd') {
      this.consume();
      return CharClasses.digit();
    }
    if (ch === 'D') {
      this.consume();
      return CharClasses.nonDigit();
    }
    if (ch === 'w') {
      this.consume();
      return CharClasses.word();
    }
    if (ch === 'W') {
      this.consume();
      return CharClasses.nonWord();
    }
    if (ch === 's') {
      this.consume();
      return CharClasses.whitespace();
    }
    if (ch === 'S') {
      this.consume();
      return CharClasses.nonWhitespace();
    }

    // Word boundary
    if (ch === 'b') {
      this.consume();
      return new Anchor('wordBoundary');
    }

    // Literal escape
    const escaped = this.parseEscapeChar();
    return new Literal(escaped);
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

/**
 * Convenience function to parse a regex pattern string into a RegexValidator
 */
export function parseRegex(source: string): RegexValidator {
  const parser = new RegexParser(source);
  return parser.parse();
}

