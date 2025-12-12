import { RegexDomain } from '../../Domain';
import { BaseRegexValidator, MatchResult } from './RegexValidator';

/**
 * Anchor kinds supported.
 * Note: Word boundaries (\b, \B) are not supported (non-portable per ADR-002)
 */
export type AnchorKind = 'start' | 'end';

/**
 * Validator for anchors (^, $)
 * Anchors match positions, not characters, so they consume nothing
 */
export class Anchor extends BaseRegexValidator {
  private readonly _domain: RegexDomain;

  constructor(public readonly kind: AnchorKind) {
    super();
    const source = this.kindToSource();
    this._domain = new RegexDomain(new RegExp(source));
  }

  get domain(): RegexDomain {
    return this._domain;
  }

  match(input: string, position: number): MatchResult {
    let matched = false;

    switch (this.kind) {
      case 'start':
        matched = position === 0;
        break;
      case 'end':
        matched = position === input.length;
        break;
    }

    // Anchors consume no characters
    return { matched, consumed: 0 };
  }

  private kindToSource(): string {
    switch (this.kind) {
      case 'start': return '^';
      case 'end': return '$';
    }
  }
}

