import { RegexDomain, DomainType } from '../../Domain';
import { RNG } from '../../RNG';
import { BaseRegexValidator, MatchResult } from './RegexValidator';

/**
 * Printable ASCII characters for the 'any' character (.)
 */
const PRINTABLE_ASCII: string[] = [];
for (let c = 32; c <= 126; c++) {
  PRINTABLE_ASCII.push(String.fromCharCode(c));
}

/**
 * Validator that matches any single character (the . metacharacter)
 * By default matches any printable ASCII character except newline
 */
export class Any extends BaseRegexValidator {
  private readonly _domain: RegexDomain;

  constructor() {
    super();
    this._domain = {
      type: DomainType.REGEX_DOMAIN,
      pattern: /./,
      source: '.',
    };
  }

  get domain(): RegexDomain {
    return this._domain;
  }

  match(input: string, position: number): MatchResult {
    if (position < input.length && input[position] !== '\n') {
      return { matched: true, consumed: 1 };
    }
    return { matched: false, consumed: 0 };
  }

  generate(rng: RNG): string {
    const index = Math.floor(rng.random() * PRINTABLE_ASCII.length);
    return PRINTABLE_ASCII[index];
  }
}

