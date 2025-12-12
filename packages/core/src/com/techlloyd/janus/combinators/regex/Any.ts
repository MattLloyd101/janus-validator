import { RegexDomain } from '../../Domain';
import { BaseRegexValidator, MatchResult } from './RegexValidator';

/**
 * Validator that matches any single character (the . metacharacter)
 * By default matches any printable ASCII character except newline
 */
export class Any extends BaseRegexValidator {
  private readonly _domain: RegexDomain;

  constructor() {
    super();
    this._domain = new RegexDomain(/./);
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
}

