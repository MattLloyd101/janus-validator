import { RegexDomain, DomainType } from '../../Domain';
import { RNG } from '../../RNG';
import { BaseRegexValidator, MatchResult } from './RegexValidator';

/**
 * Validator that matches the empty string
 * Useful as an identity element for Sequence and as a branch in Alternation
 */
export class Empty extends BaseRegexValidator {
  private readonly _domain: RegexDomain;

  constructor() {
    super();
    this._domain = {
      type: DomainType.REGEX_DOMAIN,
      pattern: /(?:)/,
      source: '',
    };
  }

  get domain(): RegexDomain {
    return this._domain;
  }

  match(_input: string, _position: number): MatchResult {
    // Empty always matches, consuming nothing
    return { matched: true, consumed: 0 };
  }

  generate(_rng: RNG): string {
    return '';
  }
}

