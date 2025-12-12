import { RegexDomain } from '../../Domain';
import { BaseRegexValidator, MatchResult } from './RegexValidator';

/**
 * Validator that matches a single literal character
 */
export class Literal extends BaseRegexValidator {
  private readonly _domain: RegexDomain;

  constructor(public readonly char: string) {
    super();
    const src = this.escapeRegex(char);
    this._domain = new RegexDomain(new RegExp(src));
  }

  get domain(): RegexDomain {
    return this._domain;
  }

  match(input: string, position: number): MatchResult {
    if (position < input.length && input[position] === this.char) {
      return { matched: true, consumed: 1 };
    }
    return { matched: false, consumed: 0 };
  }

  private escapeRegex(str: string): string {
    return str.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  }
}

