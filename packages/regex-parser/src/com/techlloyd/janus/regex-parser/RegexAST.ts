/**
 * AST node types for regex parsing and generation.
 * 
 * This AST represents regular expression patterns in a form suitable for
 * both validation and generation. Each node type corresponds to a regex
 * construct.
 */

/**
 * A contiguous range of Unicode code points (inclusive on both ends).
 * Used by CharSetDomain to efficiently represent character classes like [a-z], [0-9A-F], etc.
 */
export interface CharRange {
  readonly min: number; // Unicode code point (inclusive)
  readonly max: number; // Unicode code point (inclusive)
}

// ============================================================================
// Node Type Constants
// ============================================================================

/**
 * All possible regex AST node types
 */
export const RegexNodeType = {
  LITERAL: 'literal',
  CHAR_CLASS: 'charClass',
  ANY: 'any',
  ANCHOR: 'anchor',
  EMPTY: 'empty',
  SEQUENCE: 'sequence',
  ALTERNATION: 'alternation',
  QUANTIFIER: 'quantifier',
  GROUP: 'group',
} as const;

export type RegexNodeType = (typeof RegexNodeType)[keyof typeof RegexNodeType];

/**
 * Anchor kinds supported by the regex AST.
 * Note: Word boundaries (\b, \B) are not supported (non-portable per ADR-002)
 */
export const AnchorKind = {
  START: 'start',
  END: 'end',
} as const;

export type AnchorKind = (typeof AnchorKind)[keyof typeof AnchorKind];

// ============================================================================
// AST Node Interfaces
// ============================================================================

/**
 * A literal character node - matches exactly one character
 */
export interface LiteralNode {
  type: typeof RegexNodeType.LITERAL;
  char: string;
}

/**
 * A character class node - matches one character from a set of ranges.
 * When negated, matches any character NOT in the ranges.
 * 
 * Uses contiguous code point ranges for efficient representation:
 * - `[a-z]` is stored as `[{ min: 97, max: 122 }]`
 * - `[a-zA-Z0-9]` is stored as `[{ min: 48, max: 57 }, { min: 65, max: 90 }, { min: 97, max: 122 }]`
 */
export interface CharClassNode {
  type: typeof RegexNodeType.CHAR_CLASS;
  ranges: readonly CharRange[];
  negated: boolean;
}

/**
 * The "any" character (.) - matches any single character except newline
 */
export interface AnyNode {
  type: typeof RegexNodeType.ANY;
}

/**
 * An anchor (^, $, \b) - matches a position, not a character
 * Generates empty string
 */
export interface AnchorNode {
  type: typeof RegexNodeType.ANCHOR;
  kind: AnchorKind;
}

/**
 * Empty node - matches empty string
 */
export interface EmptyNode {
  type: typeof RegexNodeType.EMPTY;
}

/**
 * Sequence node - matches a sequence of patterns in order
 * Equivalent to concatenation in regex
 */
export interface SequenceNode {
  type: typeof RegexNodeType.SEQUENCE;
  nodes: RegexASTNode[];
}

/**
 * Alternation node - matches any one of the options
 * Equivalent to | in regex
 */
export interface AlternationNode {
  type: typeof RegexNodeType.ALTERNATION;
  options: RegexASTNode[];
}

/**
 * Quantifier node - matches the inner pattern repeated min to max times
 * Covers *, +, ?, {n}, {n,}, {n,m}
 */
export interface QuantifierNode {
  type: typeof RegexNodeType.QUANTIFIER;
  node: RegexASTNode;
  min: number;
  max: number;
}

/**
 * Group node - a grouped sub-pattern (capturing or non-capturing)
 */
export interface GroupNode {
  type: typeof RegexNodeType.GROUP;
  node: RegexASTNode;
  capturing: boolean;
}

/**
 * Union type of all regex AST nodes
 */
export type RegexASTNode =
  | LiteralNode
  | CharClassNode
  | AnyNode
  | AnchorNode
  | EmptyNode
  | SequenceNode
  | AlternationNode
  | QuantifierNode
  | GroupNode;

// ============================================================================
// Type Guards
// ============================================================================

/**
 * Type guard to check if a node is a specific type
 */
export function isLiteral(node: RegexASTNode): node is LiteralNode {
  return node.type === RegexNodeType.LITERAL;
}

export function isCharClass(node: RegexASTNode): node is CharClassNode {
  return node.type === RegexNodeType.CHAR_CLASS;
}

export function isAny(node: RegexASTNode): node is AnyNode {
  return node.type === RegexNodeType.ANY;
}

export function isAnchor(node: RegexASTNode): node is AnchorNode {
  return node.type === RegexNodeType.ANCHOR;
}

export function isEmpty(node: RegexASTNode): node is EmptyNode {
  return node.type === RegexNodeType.EMPTY;
}

export function isSequence(node: RegexASTNode): node is SequenceNode {
  return node.type === RegexNodeType.SEQUENCE;
}

export function isAlternation(node: RegexASTNode): node is AlternationNode {
  return node.type === RegexNodeType.ALTERNATION;
}

export function isQuantifier(node: RegexASTNode): node is QuantifierNode {
  return node.type === RegexNodeType.QUANTIFIER;
}

export function isGroup(node: RegexASTNode): node is GroupNode {
  return node.type === RegexNodeType.GROUP;
}
