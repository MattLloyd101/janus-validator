import { BaseDomain, Domain } from "../Domain";
import { DomainType } from "../types";
import {
  parseRegexToAST,
  RegexNodeType,
  RegexASTNode,
  CharClassNode,
  QuantifierNode,
  AlternationNode,
  SequenceNode,
  RegexASTVisitor,
} from "@janus-validator/regex-parser";
import { FiniteDomain } from "./FiniteDomain";
import { normalizeAlternation } from "./AlternationDomain";
import { ContiguousDomain } from "./ContiguousDomain";

type CharDomain = Domain<string>;
type MatchPositions = number[];

class RangeCharDomain extends ContiguousDomain<number> {
  constructor(min: number, max: number) {
    super(min, max);
  }
}

class CharRangeAdapter extends BaseDomain<string> {
  readonly kind = DomainType.CONTIGUOUS;
  constructor(private readonly range: RangeCharDomain) {
    super();
  }
  contains(value: unknown): value is string {
    if (typeof value !== "string" || value.length === 0) return false;
    const cp = value.codePointAt(0)!;
    return this.range.contains(cp);
  }
}

type MatchContext = { value: string; pos: number };

class RegexAstGuardVisitor extends RegexASTVisitor<void, void> {
  protected visitLiteral(): void { return; }
  protected visitCharClass(node: CharClassNode): void {
    if (node.negated) {
      throw new Error("Unsupported regex construct: negated character class");
    }
  }
  protected visitAny(): void { return; }
  protected visitAnchor(): void { return; }
  protected visitEmpty(): void { return; }
  protected visitSequence(node: SequenceNode): void {
    node.nodes.forEach((child) => this.visit(child, undefined));
  }
  protected visitAlternation(node: AlternationNode): void {
    node.options.forEach((opt) => this.visit(opt, undefined));
  }
  protected visitQuantifier(node: QuantifierNode): void {
    this.visit(node.node, undefined);
  }
  protected visitGroup(node: { node: RegexASTNode }): void {
    this.visit(node.node, undefined);
  }
}

class RegexMatchVisitor extends RegexASTVisitor<MatchPositions, MatchContext> {
  /**
   * Traverses the regex AST and returns all possible end offsets (positions into the string)
   * reachable after matching starting at ctx.pos. A full-string match is detected by checking
   * whether the returned offsets include value.length at the call site. Note: offsets advance
   * per JS string index (UTF-16 code units); if we later need full code-point semantics, both
   * traversal and the end check must switch to code-point iteration.
   */
  protected visitLiteral(node: any, ctx: MatchContext): MatchPositions {
    return new FiniteDomain([node.char]).contains(ctx.value[ctx.pos]) ? [ctx.pos + 1] : [];
  }

  protected visitCharClass(node: CharClassNode, ctx: MatchContext): MatchPositions {
    const domain: CharDomain =
      node.ranges.length === 1
        ? new CharRangeAdapter(new RangeCharDomain(node.ranges[0].min, node.ranges[0].max))
        : normalizeAlternation(node.ranges.map((r) => new CharRangeAdapter(new RangeCharDomain(r.min, r.max))));

    return domain.contains(ctx.value[ctx.pos]) ? [ctx.pos + 1] : [];
  }

  protected visitAny(_node: any, ctx: MatchContext): MatchPositions {
    const domain = new CharRangeAdapter(new RangeCharDomain(32, 126));
    return domain.contains(ctx.value[ctx.pos]) ? [ctx.pos + 1] : [];
  }

  protected visitAnchor(node: any, ctx: MatchContext): MatchPositions {
    if (node.kind === "start") return ctx.pos === 0 ? [ctx.pos] : [];
    if (node.kind === "end") return ctx.pos === ctx.value.length ? [ctx.pos] : [];
    
    return [];
  }

  protected visitEmpty(_node: any, ctx: MatchContext): MatchPositions {
    return [ctx.pos];
  }

  protected visitSequence(node: SequenceNode, ctx: MatchContext): MatchPositions {
    let positions: MatchPositions = [ctx.pos];
    for (const child of node.nodes) {
      const next: MatchPositions = [];
      for (const p of positions) {
        next.push(...this.visit(child, { ...ctx, pos: p }));
      }
      positions = Array.from(new Set(next));
      if (positions.length === 0) break;
    }
    return positions;
  }

  protected visitAlternation(node: AlternationNode, ctx: MatchContext): MatchPositions {
    const positions = new Set<number>();
    for (const opt of node.options) {
      this.visit(opt, ctx).forEach((p) => positions.add(p));
    }
    return Array.from(positions);
  }

  protected visitQuantifier(node: QuantifierNode, ctx: MatchContext): MatchPositions {
    const results = new Set<number>();
    const self = this;

    function backtrack(currentPos: number, count: number): void {
      if (count >= node.min) {
        results.add(currentPos);
      }
      if (node.max !== undefined && count === node.max) return;
      const nextPositions = self.visit(node.node, { ...ctx, pos: currentPos });
      for (const nextPos of nextPositions) {
        if (nextPos === currentPos) continue; // avoid infinite loop on empty
        backtrack(nextPos, count + 1);
      }
    }

    backtrack(ctx.pos, 0);
    return Array.from(results);
  }

  protected visitGroup(node: { node: RegexASTNode }, ctx: MatchContext): MatchPositions {
    return this.visit(node.node, ctx);
  }
}

export class RegexDomain extends BaseDomain<string> {
  readonly kind = DomainType.REGEX;
  readonly source: string;
  readonly ast: RegexASTNode;
  readonly pattern: RegExp;
  private readonly matcher = new RegexMatchVisitor();
  private readonly guard = new RegexAstGuardVisitor();

  constructor(pattern: RegExp) {
    super();
    this.source = pattern.source;
    this.ast = parseRegexToAST(pattern.source, pattern.flags);
    this.pattern = new RegExp(pattern.source, pattern.flags);
    this.guard.visit(this.ast, undefined);
  }

  contains(value: unknown): value is string {
    if (typeof value !== "string") return false;
    const positions = this.matcher.visit(this.ast, { value, pos: 0 });
    return positions.includes(value.length);
  }
}

// Exposed only for tests to exercise defensive branches
export { RegexMatchVisitor as _RegexMatchVisitorTestOnly };

