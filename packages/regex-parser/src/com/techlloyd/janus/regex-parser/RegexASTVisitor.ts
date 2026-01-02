import {
  RegexASTNode,
  RegexNodeType,
  LiteralNode,
  CharClassNode,
  AnyNode,
  AnchorNode,
  EmptyNode,
  SequenceNode,
  AlternationNode,
  QuantifierNode,
  GroupNode,
} from "./RegexAST";

/**
  * Base visitor for Regex AST nodes.
  *
  * - `R` is the return type of each visit method.
  * - `C` is an optional context passed through the traversal (e.g., carry state like position or accumulator).
  *
  * Subclasses implement one method per node type; the `visit` dispatcher calls the corresponding method.
  */
export abstract class RegexASTVisitor<R, C = undefined> {
  visit(node: RegexASTNode, ctx: C): R {
    switch (node.type) {
      case RegexNodeType.LITERAL:
        return this.visitLiteral(node as LiteralNode, ctx);
      case RegexNodeType.CHAR_CLASS:
        return this.visitCharClass(node as CharClassNode, ctx);
      case RegexNodeType.ANY:
        return this.visitAny(node as AnyNode, ctx);
      case RegexNodeType.ANCHOR:
        return this.visitAnchor(node as AnchorNode, ctx);
      case RegexNodeType.EMPTY:
        return this.visitEmpty(node as EmptyNode, ctx);
      case RegexNodeType.SEQUENCE:
        return this.visitSequence(node as SequenceNode, ctx);
      case RegexNodeType.ALTERNATION:
        return this.visitAlternation(node as AlternationNode, ctx);
      case RegexNodeType.QUANTIFIER:
        return this.visitQuantifier(node as QuantifierNode, ctx);
      case RegexNodeType.GROUP:
        return this.visitGroup(node as GroupNode, ctx);
      default:
        return this.visitUnsupported(node, ctx);
    }
  }

  protected visitUnsupported(node: RegexASTNode, _ctx: C): R {
    throw new Error(`Unsupported regex AST node type: ${node.type}`);
  }

  protected abstract visitLiteral(node: LiteralNode, ctx: C): R;
  protected abstract visitCharClass(node: CharClassNode, ctx: C): R;
  protected abstract visitAny(node: AnyNode, ctx: C): R;
  protected abstract visitAnchor(node: AnchorNode, ctx: C): R;
  protected abstract visitEmpty(node: EmptyNode, ctx: C): R;
  protected abstract visitSequence(node: SequenceNode, ctx: C): R;
  protected abstract visitAlternation(node: AlternationNode, ctx: C): R;
  protected abstract visitQuantifier(node: QuantifierNode, ctx: C): R;
  protected abstract visitGroup(node: GroupNode, ctx: C): R;
}

