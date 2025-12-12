import { RegexDomain, DomainType } from '../../Domain';
import { BaseRegexValidator, MatchResult } from './RegexValidator';

/**
 * Validator that matches one character from a set of characters
 * Supports both positive [abc] and negated [^abc] character classes
 */
export class CharClass extends BaseRegexValidator {
  private readonly _domain: RegexDomain;
  private readonly charSet: Set<string>;

  constructor(
    public readonly chars: string[],
    public readonly negated: boolean = false
  ) {
    super();
    this.charSet = new Set(chars);
    
    const source = this.buildSource();
    this._domain = {
      type: DomainType.REGEX_DOMAIN,
      pattern: new RegExp(source),
      source,
    };
  }

  get domain(): RegexDomain {
    return this._domain;
  }

  match(input: string, position: number): MatchResult {
    if (position >= input.length) {
      return { matched: false, consumed: 0 };
    }

    const char = input[position];
    const inSet = this.charSet.has(char);
    const matched = this.negated ? !inSet : inSet;

    return { matched, consumed: matched ? 1 : 0 };
  }

  private buildSource(): string {
    const escaped = this.chars.map(c => this.escapeForCharClass(c)).join('');
    return this.negated ? `[^${escaped}]` : `[${escaped}]`;
  }

  private escapeForCharClass(char: string): string {
    if (char === ']' || char === '\\' || char === '^' || char === '-') {
      return '\\' + char;
    }
    return char;
  }
}

/**
 * Common character class factories
 */
export const CharClasses = {
  /** Matches any digit [0-9] */
  digit(): CharClass {
    return new CharClass(['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']);
  },

  /** Matches any non-digit [^0-9] */
  nonDigit(): CharClass {
    return new CharClass(['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'], true);
  },

  /** Matches any word character [a-zA-Z0-9_] */
  word(): CharClass {
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
    return new CharClass(chars);
  },

  /** Matches any non-word character [^a-zA-Z0-9_] */
  nonWord(): CharClass {
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
    return new CharClass(chars, true);
  },

  /** Matches any whitespace character */
  whitespace(): CharClass {
    return new CharClass([' ', '\t', '\n', '\r', '\f', '\v']);
  },

  /** Matches any non-whitespace character */
  nonWhitespace(): CharClass {
    return new CharClass([' ', '\t', '\n', '\r', '\f', '\v'], true);
  },

  /** Creates a character range, e.g., 'a' to 'z' */
  range(start: string, end: string): CharClass {
    const chars: string[] = [];
    for (let c = start.charCodeAt(0); c <= end.charCodeAt(0); c++) {
      chars.push(String.fromCharCode(c));
    }
    return new CharClass(chars);
  },
};

