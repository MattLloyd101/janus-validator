import { RegexValidator } from './RegexValidator';
import { Literal } from './Literal';
import { CharClass } from './CharClass';
import { Any } from './Any';
import { Empty } from './Empty';
import { Anchor } from './Anchor';
import { RegexSequence } from './Sequence';
import { RegexAlternation } from './Alternation';
import { Quantifier } from './Quantifier';
import { Group } from './Group';
import { parseRegexToAST, RegexASTNode, RegexNodeType } from '../../regex';

/**
 * Converts a RegexAST node into a composed RegexValidator.
 * 
 * This function recursively traverses the AST produced by the regex parser
 * and creates the corresponding validator instances for each node type.
 * 
 * @param node - The AST node to convert
 * @returns A RegexValidator that validates the pattern represented by the AST
 * 
 * @example
 * ```typescript
 * import { parseRegexToAST } from '../../regex';
 * 
 * const ast = parseRegexToAST('[a-z]+');
 * const validator = astToValidator(ast);
 * validator.validate('hello'); // valid
 * ```
 */
export function astToValidator(node: RegexASTNode): RegexValidator {
  switch (node.type) {
    case RegexNodeType.LITERAL:
      return new Literal(node.char);

    case RegexNodeType.CHAR_CLASS:
      return new CharClass(node.chars, node.negated);

    case RegexNodeType.ANY:
      return new Any();

    case RegexNodeType.ANCHOR:
      return new Anchor(node.kind);

    case RegexNodeType.EMPTY:
      return new Empty();

    case RegexNodeType.SEQUENCE:
      return RegexSequence.create(...node.nodes.map(n => astToValidator(n)));

    case RegexNodeType.ALTERNATION:
      return RegexAlternation.create(...node.options.map(n => astToValidator(n)));

    case RegexNodeType.QUANTIFIER:
      return new Quantifier(astToValidator(node.node), node.min, node.max);

    case RegexNodeType.GROUP:
      return new Group(astToValidator(node.node), node.capturing);
  }
}

/**
 * Parse a regex pattern string into a composed RegexValidator.
 * 
 * This is a convenience function that:
 * 1. Parses the pattern string into an AST using the shared regex parser
 * 2. Converts the AST into a tree of RegexValidator instances
 * 
 * Supports:
 * - Literals and escaped characters
 * - Character classes: [abc], [a-z], [^abc]
 * - Quantifiers: *, +, ?, {n}, {n,}, {n,m}
 * - Groups: (abc), (?:abc)
 * - Alternation: a|b
 * - Anchors: ^, $
 * - Any character: .
 * - Common escape sequences: \d, \w, \s, etc.
 * 
 * @param source - The regex pattern string to parse
 * @returns A RegexValidator that validates the pattern
 * 
 * @example
 * ```typescript
 * const validator = parseRegex('[a-z]+@[a-z]+\\.[a-z]{2,3}');
 * validator.validate('test@example.com'); // valid
 * ```
 */
export function parseRegex(source: string): RegexValidator {
  const ast = parseRegexToAST(source);
  return astToValidator(ast);
}
