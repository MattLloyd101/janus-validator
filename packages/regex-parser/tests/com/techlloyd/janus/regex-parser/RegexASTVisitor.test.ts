import { RegexASTVisitor, RegexNodeType, parseRegexToAST } from "@/com/techlloyd/janus/regex-parser";

class RecordingVisitor extends RegexASTVisitor<void, { events: string[] }> {
  protected visitLiteral(node: any, ctx: { events: string[] }) {
    ctx.events.push(`L:${node.char}`);
  }
  protected visitCharClass(node: any, ctx: { events: string[] }) {
    ctx.events.push("CharClass");
  }
  protected visitAny(_node: any, ctx: { events: string[] }) {
    ctx.events.push("Any");
  }
  protected visitAnchor(node: any, ctx: { events: string[] }) {
    ctx.events.push(`Anchor:${node.kind}`);
  }
  protected visitEmpty(_node: any, ctx: { events: string[] }) {
    ctx.events.push("Empty");
  }
  protected visitSequence(node: any, ctx: { events: string[] }) {
    ctx.events.push("Seq");
    node.nodes.forEach((child: any) => this.visit(child, ctx));
  }
  protected visitAlternation(node: any, ctx: { events: string[] }) {
    ctx.events.push("Alt");
    node.options.forEach((opt: any) => this.visit(opt, ctx));
  }
  protected visitQuantifier(node: any, ctx: { events: string[] }) {
    ctx.events.push(`Quant:${node.min}-${node.max}`);
    this.visit(node.node, ctx);
  }
  protected visitGroup(node: any, ctx: { events: string[] }) {
    ctx.events.push("Group");
    this.visit(node.node, ctx);
  }
}

class CountingVisitor extends RegexASTVisitor<number, void> {
  protected visitLiteral(): number { return 1; }
  protected visitCharClass(): number { return 1; }
  protected visitAny(): number { return 1; }
  protected visitAnchor(): number { return 1; }
  protected visitEmpty(): number { return 1; }
  protected visitSequence(node: any): number {
    return 1 + node.nodes.reduce((sum: number, child: any) => sum + this.visit(child, undefined), 0);
  }
  protected visitAlternation(node: any): number {
    return 1 + node.options.reduce((sum: number, child: any) => sum + this.visit(child, undefined), 0);
  }
  protected visitQuantifier(node: any): number {
    return 1 + this.visit(node.node, undefined);
  }
  protected visitGroup(node: any): number {
    return 1 + this.visit(node.node, undefined);
  }
}

describe("RegexASTVisitor", () => {
  it("dispatches to specific visit methods with context", () => {
    const ast = parseRegexToAST("(?:a|b{2,3})c");
    const events: string[] = [];
    new RecordingVisitor().visit(ast, { events });
    expect(events).toEqual([
      "Seq",
      "Group",
      "Alt",
      "L:a",
      "Quant:2-3",
      "L:b",
      "L:c",
    ]);
  });

  it("can aggregate results across the tree", () => {
    const ast = parseRegexToAST("^a?$");
    const nodeCount = new CountingVisitor().visit(ast, undefined);
    expect(nodeCount).toBeGreaterThan(0);
    // Sequence + Anchor + Quantifier + Literal + Anchor
    expect(nodeCount).toBeGreaterThanOrEqual(5);
  });
});

