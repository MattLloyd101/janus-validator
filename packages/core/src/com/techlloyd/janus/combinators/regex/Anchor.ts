import { RegexDomain, DomainType } from '../../Domain';
import { BaseRegexValidator, MatchResult } from './RegexValidator';

export type AnchorKind = 'start' | 'end' | 'wordBoundary';

/**
 * Validator for anchors (^, $, \b)
 * Anchors match positions, not characters, so they consume nothing
 */
export class Anchor extends BaseRegexValidator {
  private readonly _domain: RegexDomain;

  constructor(public readonly kind: AnchorKind) {
    super();
    const source = this.kindToSource();
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
    let matched = false;

    switch (this.kind) {
      case 'start':
        matched = position === 0;
        break;
      case 'end':
        matched = position === input.length;
        break;
      case 'wordBoundary':
        matched = this.isWordBoundary(input, position);
        break;
    }

    // Anchors consume no characters
    return { matched, consumed: 0 };
  }

  private kindToSource(): string {
    switch (this.kind) {
      case 'start': return '^';
      case 'end': return '$';
      case 'wordBoundary': return '\\b';
    }
  }

  private isWordBoundary(input: string, position: number): boolean {
    const isWord = (char: string | undefined) => {
      if (!char) return false;
      return /\w/.test(char);
    };

    const before = position > 0 ? input[position - 1] : undefined;
    const after = position < input.length ? input[position] : undefined;

    return isWord(before) !== isWord(after);
  }
}

