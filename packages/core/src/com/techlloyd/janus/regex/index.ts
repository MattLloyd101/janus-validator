/**
 * Regex AST and Parser module
 * 
 * Provides a shared regex AST and parser that can be used by both:
 * - Domain generators (for generating matching strings)
 * - Combinator validators (for creating validator trees)
 */

export {
  // Constants
  RegexNodeType,
  AnchorKind,
  // AST Node types
  RegexASTNode,
  LiteralNode,
  CharClassNode,
  AnyNode,
  AnchorNode,
  EmptyNode,
  SequenceNode,
  AlternationNode,
  QuantifierNode,
  GroupNode,
  // Type guards
  isLiteral,
  isCharClass,
  isAny,
  isAnchor,
  isEmpty,
  isSequence,
  isAlternation,
  isQuantifier,
  isGroup,
} from './RegexAST';

export { parseRegexToAST } from './RegexASTParser';

