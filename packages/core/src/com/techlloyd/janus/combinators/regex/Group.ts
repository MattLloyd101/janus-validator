import { RegexDomain, DomainType } from '../../Domain';
import { BaseRegexValidator, MatchResult, RegexValidator } from './RegexValidator';

/**
 * Group combinator that wraps a validator in a group.
 * 
 * Groups can be capturing or non-capturing.
 * For validation purposes, they behave the same as their inner validator.
 */
export class Group extends BaseRegexValidator {
  private readonly _domain: RegexDomain;

  constructor(
    public readonly validator: RegexValidator,
    public readonly capturing: boolean = true
  ) {
    super();
    
    const inner = (validator.domain as RegexDomain).source;
    const source = capturing ? `(${inner})` : `(?:${inner})`;
    
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
    // Groups just delegate to their inner validator
    return this.validator.match(input, position);
  }

  /**
   * Factory methods
   */
  static capturing(validator: RegexValidator): Group {
    return new Group(validator, true);
  }

  static nonCapturing(validator: RegexValidator): Group {
    return new Group(validator, false);
  }
}

