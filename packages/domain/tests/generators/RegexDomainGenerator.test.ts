import { RegexDomain } from "@/domains/RegexDomain";
import { RegexDomainGenerator } from "@/generators/RegexDomainGenerator";
import { rngFromSequence } from "./helpers";
import { RegexNodeType } from "@janus-validator/regex-parser";

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
    const gen = new RegexDomainGenerator() as any;
    const rng = rngFromSequence([0.2, 0.4, 0.6, 0.8]);

    // Char class branch
    const char = gen.generateFromAST(
      { type: RegexNodeType.CHAR_CLASS, ranges: [{ min: 48, max: 57 }], negated: false },
      rng
    );
    expect(char).toMatch(/[0-9]/);

    // ANY branch
    const any = gen.generateFromAST({ type: RegexNodeType.ANY } as any, rng);
    expect(any.length).toBe(1);

    // QUANTIFIER branch with Infinity
    const quant = gen.generateFromAST(
      { type: RegexNodeType.QUANTIFIER, node: { type: RegexNodeType.LITERAL, char: "a" }, min: 1, max: Infinity },
      rng
    );
    expect(quant.length).toBeGreaterThanOrEqual(1);

    // ANCHOR/EMPTY branches
    const empty = gen.generateFromAST({ type: RegexNodeType.EMPTY } as any, rng);
    expect(empty).toBe("");
  });
});

