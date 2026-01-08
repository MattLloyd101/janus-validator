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
import {
  parseRegexToAST,
  RegexASTNode,
  RegexASTVisitor,
  LiteralNode,
  CharClassNode,
  AnyNode,
  AnchorNode,
  EmptyNode,
  SequenceNode,
  AlternationNode,
  QuantifierNode,
  GroupNode,
} from '@janus-validator/regex-parser';

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
class RegexValidatorBuilder extends RegexASTVisitor<RegexValidator, void> {
  protected visitLiteral(node: LiteralNode): RegexValidator {
    return new Literal(node.char);
  }

  protected visitCharClass(node: CharClassNode): RegexValidator {
    return new CharClass(node.ranges, node.negated);
  }

  protected visitAny(_node: AnyNode): RegexValidator {
    return new Any();
  }

  protected visitAnchor(node: AnchorNode): RegexValidator {
    return new Anchor(node.kind);
  }

  protected visitEmpty(_node: EmptyNode): RegexValidator {
    return new Empty();
  }

  protected visitSequence(node: SequenceNode): RegexValidator {
    const parts = node.nodes.map((n: RegexASTNode) => this.visit(n, undefined));
    return RegexSequence.create(...parts);
  }

  protected visitAlternation(node: AlternationNode): RegexValidator {
    const options = node.options.map((n: RegexASTNode) => this.visit(n, undefined));
    return RegexAlternation.create(...options);
  }

  protected visitQuantifier(node: QuantifierNode): RegexValidator {
    return new Quantifier(this.visit(node.node, undefined), node.min, node.max);
  }

  protected visitGroup(node: GroupNode): RegexValidator {
    return new Group(this.visit(node.node, undefined), node.capturing);
  }
}

const builder = new RegexValidatorBuilder();

export function astToValidator(node: RegexASTNode): RegexValidator {
  return builder.visit(node, undefined);
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
export function parseRegex(source: string, flags: string = ''): RegexValidator {
  const ast = parseRegexToAST(source, flags);
  return astToValidator(ast);
}
