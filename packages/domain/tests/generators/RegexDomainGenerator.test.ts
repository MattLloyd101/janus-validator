import { RegexDomain } from "@/domains/RegexDomain";
import { RegexDomainGenerator } from "@/generators/RegexDomainGenerator";
import { rngFromSequence } from "./helpers";
import { RegexNodeType, CharClassNode, AnyNode, QuantifierNode, LiteralNode, EmptyNode } from "@janus-validator/regex-parser";

describe("RegexDomainGenerator", () => {
  it("generates strings matching simple patterns", () => {
    const gen = new RegexDomainGenerator();
    const domain = new RegexDomain(/^[a-c]{3}$/);
    const rng = rngFromSequence([0.1, 0.2, 0.3]);
    const value = gen.generate(domain, rng);
    expect(domain.contains(value)).toBe(true);
  });

  it("handles alternation", () => {
    const gen = new RegexDomainGenerator();
    const domain = new RegexDomain(/^(foo|bar)$/);
    const rng = rngFromSequence([0.05]);
    const value = gen.generate(domain, rng);
    expect(["foo", "bar"]).toContain(value);
  });

  it("handles any/dot and anchors", () => {
    const gen = new RegexDomainGenerator();
    const domain = new RegexDomain(/^.$/);
    const rng = rngFromSequence([0.2]);
    const value = gen.generate(domain, rng);
    expect(domain.contains(value)).toBe(true);
  });

  it("handles unbounded quantifier with cap", () => {
    const gen = new RegexDomainGenerator();
    const domain = new RegexDomain(/^a+$/);
    const rng = rngFromSequence([0.1, 0.2, 0.3]);
    const value = gen.generate(domain, rng);
    expect(domain.contains(value)).toBe(true);
    expect(value.length).toBeGreaterThanOrEqual(1);
  });

  it("handles empty/anchor patterns", () => {
    const gen = new RegexDomainGenerator();
    const domain = new RegexDomain(/^$/);
    const rng = rngFromSequence([0.1]);
    const value = gen.generate(domain, rng);
    expect(value).toBe("");
    expect(domain.contains(value)).toBe(true);
  });

  it("covers generator branches directly", () => {
    const gen = new RegexDomainGenerator();
    // Access generateFromAST via `any` to bypass private access for testing internal behavior
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    const genAny = gen as any;
    const rng = rngFromSequence([0.2, 0.4, 0.6, 0.8]);

    // Char class branch
    const charClassNode: CharClassNode = {
      type: RegexNodeType.CHAR_CLASS,
      ranges: [{ min: 48, max: 57 }],
      negated: false
    };
    const char = genAny.generateFromAST(charClassNode, rng);
    expect(char).toMatch(/[0-9]/);

    // ANY branch
    const anyNode: AnyNode = { type: RegexNodeType.ANY };
    const any = genAny.generateFromAST(anyNode, rng);
    expect(any.length).toBe(1);

    // QUANTIFIER branch with Infinity
    const literalNode: LiteralNode = { type: RegexNodeType.LITERAL, char: "a" };
    const quantNode: QuantifierNode = {
      type: RegexNodeType.QUANTIFIER,
      node: literalNode,
      min: 1,
      max: Infinity
    };
    const quant = genAny.generateFromAST(quantNode, rng);
    expect(quant.length).toBeGreaterThanOrEqual(1);

    // ANCHOR/EMPTY branches
    const emptyNode: EmptyNode = { type: RegexNodeType.EMPTY };
    const empty = genAny.generateFromAST(emptyNode, rng);
    expect(empty).toBe("");
  });
});
