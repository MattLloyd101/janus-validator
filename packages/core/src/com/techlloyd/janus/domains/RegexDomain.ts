/**
 * Regex domain for strings matching a regular expression pattern.
 * The pattern is stored as both a RegExp and its source string for parsing.
 */

import { Domain } from './Domain';
import { DomainType, RelationResult, ok, no, unknown } from './types';
import { rangesSubset } from './CharRange';
import { parseRegexToAST, RegexASTNode, RegexNodeType } from '../regex';

export class RegexDomain extends Domain<string> {
  readonly type = DomainType.REGEX_DOMAIN;
  readonly source: string;

  constructor(public readonly pattern: RegExp) {
    super();
    this.source = pattern.source;
  }

  protected encapsulatesImpl(other: Domain<string>): RelationResult {
    if (!(other instanceof RegexDomain)) {
      return no(`Domain type mismatch: ${other.type} not subset of ${this.type}`);
    }

    // Quick equality check
    if (this.source === other.source) return ok();

    // Parse both to AST and compare structurally
    try {
      const thisAST = parseRegexToAST(this.source);
      const otherAST = parseRegexToAST(other.source);
      return astEncapsulates(thisAST, otherAST);
    } catch {
      return unknown('Failed to parse regex for comparison');
    }
  }
}

/**
 * Check if AST node `a` encapsulates AST node `b`.
 * Returns true iff every string matched by `b` is also matched by `a`.
 */
function astEncapsulates(a: RegexASTNode, b: RegexASTNode): RelationResult {
  // Unwrap groups (they're transparent for matching)
  const a0 = unwrapGroups(a);
  const b0 = unwrapGroups(b);

  // If `a` is an alternation, it encapsulates `b` if ANY alternative encapsulates `b`
  if (a0.type === RegexNodeType.ALTERNATION) {
    for (const opt of a0.options) {
      const res = astEncapsulates(opt, b0);
      if (res.result === 'true') return ok();
    }
    return no('No alternation branch encapsulates the pattern');
  }

  // If `b` is an alternation, `a` must encapsulate ALL alternatives in `b`
  if (b0.type === RegexNodeType.ALTERNATION) {
    for (const opt of b0.options) {
      const res = astEncapsulates(a0, opt);
      if (res.result !== 'true') return res;
    }
    return ok();
  }

  // Same type comparisons
  switch (b0.type) {
    case RegexNodeType.EMPTY:
      return a0.type === RegexNodeType.EMPTY ? ok() : no('Empty pattern mismatch');

    case RegexNodeType.ANCHOR:
      if (a0.type !== RegexNodeType.ANCHOR) return no('Anchor type mismatch');
      return a0.kind === b0.kind ? ok() : no(`Anchor kind mismatch: ${a0.kind} vs ${b0.kind}`);

    case RegexNodeType.LITERAL:
      // Literal can be encapsulated by: same literal, charclass containing it, or any
      if (a0.type === RegexNodeType.LITERAL) {
        return a0.char === b0.char ? ok() : no(`Literal mismatch: '${a0.char}' vs '${b0.char}'`);
      }
      if (a0.type === RegexNodeType.CHAR_CLASS && !a0.negated) {
        const cp = b0.char.codePointAt(0)!;
        const covered = a0.ranges.some(r => cp >= r.min && cp <= r.max);
        return covered ? ok() : no(`Literal '${b0.char}' not in char class`);
      }
      if (a0.type === RegexNodeType.ANY) {
        // Any matches any single char (except newline, but we ignore that for encapsulation)
        return ok();
      }
      return no(`Literal cannot be encapsulated by ${a0.type}`);

    case RegexNodeType.CHAR_CLASS:
      // CharClass can be encapsulated by: superset charclass, or any (if not negated)
      if (a0.type === RegexNodeType.CHAR_CLASS) {
        if (b0.negated !== a0.negated) {
          return unknown('Negated vs non-negated char class comparison not supported');
        }
        if (!b0.negated && !a0.negated) {
          // Both positive: a must contain all chars in b
          return rangesSubset(a0.ranges, b0.ranges)
            ? ok()
            : no('Char class ranges not covered');
        }
        // Both negated: a must exclude subset of what b excludes (i.e., b.ranges ⊆ a.ranges)
        return rangesSubset(b0.ranges, a0.ranges)
          ? ok()
          : no('Negated char class not encapsulated');
      }
      if (a0.type === RegexNodeType.ANY && !b0.negated) {
        return ok(); // Any encapsulates any positive char class
      }
      return no(`CharClass cannot be encapsulated by ${a0.type}`);

    case RegexNodeType.ANY:
      // Any can only be encapsulated by any
      return a0.type === RegexNodeType.ANY ? ok() : no(`Any cannot be encapsulated by ${a0.type}`);

    case RegexNodeType.SEQUENCE:
      if (a0.type !== RegexNodeType.SEQUENCE) {
        // Single node `a` can encapsulate sequence `b` only if b has length 1
        if (b0.nodes.length === 1) {
          return astEncapsulates(a0, b0.nodes[0]);
        }
        return no(`Sequence cannot be encapsulated by ${a0.type}`);
      }
      if (a0.nodes.length !== b0.nodes.length) {
        return no(`Sequence length mismatch: ${a0.nodes.length} vs ${b0.nodes.length}`);
      }
      for (let i = 0; i < b0.nodes.length; i++) {
        const res = astEncapsulates(a0.nodes[i], b0.nodes[i]);
        if (res.result !== 'true') return res;
      }
      return ok();

    case RegexNodeType.QUANTIFIER:
      if (a0.type !== RegexNodeType.QUANTIFIER) {
        return no(`Quantifier cannot be encapsulated by ${a0.type}`);
      }
      // a{minA,maxA} encapsulates b{minB,maxB} iff minA <= minB && maxA >= maxB
      // AND the inner patterns are compatible
      if (a0.min > b0.min) return no(`Quantifier min ${b0.min} < ${a0.min}`);
      if (a0.max < b0.max) return no(`Quantifier max ${b0.max} > ${a0.max}`);
      return astEncapsulates(a0.node, b0.node);

    case RegexNodeType.GROUP:
      // Already unwrapped, shouldn't reach here
      return astEncapsulates(a0, b0.node);

    default:
      return unknown(`Unsupported AST node type for comparison`);
  }
}

/**
 * Unwrap group nodes to get the inner pattern.
 */
function unwrapGroups(node: RegexASTNode): RegexASTNode {
  let cur = node;
  while (cur.type === RegexNodeType.GROUP) {
    cur = cur.node;
  }
  return cur;
}
