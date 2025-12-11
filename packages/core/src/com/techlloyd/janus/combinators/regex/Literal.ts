import { RegexDomain, DomainType } from '../../Domain';
import { RNG } from '../../RNG';
import { BaseRegexValidator, MatchResult } from './RegexValidator';

/**
 * Validator that matches a single literal character
 */
export class Literal extends BaseRegexValidator {
  private readonly _domain: RegexDomain;

  constructor(public readonly char: string) {
    super();
    this._domain = {
      type: DomainType.REGEX_DOMAIN,
      pattern: new RegExp(this.escapeRegex(char)),
      source: this.escapeRegex(char),
    };
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

  generate(_rng: RNG): string {
    return this.char;
  }

  private escapeRegex(str: string): string {
    return str.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  }
}

