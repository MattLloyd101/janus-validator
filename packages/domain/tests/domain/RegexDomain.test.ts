import { RegexDomain, _RegexMatchVisitorTestOnly } from "@/domains/RegexDomain";
import { RegexNodeType, AnchorNode } from "@janus-validator/regex-parser";

describe("RegexDomain guardrails", () => {
  it("rejects lookarounds and backreferences", () => {
    expect(() => new RegexDomain(/a(?=b)/)).toThrow("Unsupported regex construct");
    expect(() => new RegexDomain(/(a)\1/)).toThrow("Unsupported regex construct");
  });

  it("rejects ambiguous escapes", () => {
    expect(() => new RegexDomain(/\w+/)).toThrow(/not portable/);
    expect(() => new RegexDomain(/\s+/)).toThrow(/not portable/);
  });

  it("accepts portable patterns", () => {
    const domain = new RegexDomain(/^[A-Za-z0-9_]+$/);
    expect(domain.contains("abc_123")).toBe(true);
    expect(domain.contains("abc-123")).toBe(false);
  });

  it("supports bounded quantifiers", () => {
    const domain = new RegexDomain(/^[ab]{2,3}$/);
    expect(domain.contains("aa")).toBe(true);
    expect(domain.contains("aaa")).toBe(true);
    expect(domain.contains("aaaa")).toBe(false);
  });

  it("rejects negated classes as unsupported", () => {
    expect(() => new RegexDomain(/[^a]/)).toThrow("Unsupported regex construct");
  });

  it("handles empty and anchors", () => {
    const domain = new RegexDomain(/^$/);
    expect(domain.contains("")).toBe(true);
    expect(domain.contains("a")).toBe(false);
  });

  it("supports alternation", () => {
    const domain = new RegexDomain(/^(foo|bar)$/);
    expect(domain.contains("foo")).toBe(true);
    expect(domain.contains("baz")).toBe(false);
  });

  it("handles anchors correctly", () => {
    const domain = new RegexDomain(/^abc$/);
    expect(domain.contains("abc")).toBe(true);
    expect(domain.contains("xabc")).toBe(false);
    expect(domain.contains("abcx")).toBe(false);
  });

  it("handles dot (any) for printable ascii only", () => {
    const domain = new RegexDomain(/^.$/);
    expect(domain.contains("A")).toBe(true);
    expect(domain.contains("\n")).toBe(false);
  });

  it("matches grouped quantified optional", () => {
    const domain = new RegexDomain(/^(ab)?c$/);
    expect(domain.contains("c")).toBe(true);
    expect(domain.contains("abc")).toBe(true);
    expect(domain.contains("abbc")).toBe(false);
  });

  it("matches empty pattern", () => {
    const domain = new RegexDomain(/^()$/);
    expect(domain.contains("")).toBe(true);
    expect(domain.contains("a")).toBe(false);
  });

  it("handles zero-length quantifier", () => {
    const domain = new RegexDomain(/^a{0,0}$/);
    expect(domain.contains("")).toBe(true);
    expect(domain.contains("a")).toBe(false);
  });

  it("returns false for non-string inputs", () => {
    const domain = new RegexDomain(/^[a]+$/);
    // Testing defensive behavior - domain.contains should handle non-strings
    expect(domain.contains(123)).toBe(false);
  });

  it("honors start and end anchors", () => {
    const startOnly = new RegexDomain(/^abc/);
    expect(startOnly.contains("abc")).toBe(true);
    expect(startOnly.contains("zabc")).toBe(false);

    const endOnly = new RegexDomain(/abc$/);
    expect(endOnly.contains("abc")).toBe(true);
    expect(endOnly.contains("abcz")).toBe(false);
  });

  it("supports multi-range character classes", () => {
    const domain = new RegexDomain(/^[a-cx-z]$/);
    expect(domain.contains("b")).toBe(true);
    expect(domain.contains("y")).toBe(true);
    expect(domain.contains("d")).toBe(false);
  });

  it("throws on flags for portability", () => {
    expect(() => new RegexDomain(/abc/i)).toThrow(/Unsupported regex flags/);
  });

  it("defensive anchor path returns empty for unknown kind", () => {
    const visitor = new _RegexMatchVisitorTestOnly();
    // Test defensive behavior with an invalid anchor kind
    const invalidAnchor: AnchorNode = {
      type: RegexNodeType.ANCHOR,
      kind: "bogus" as "start" | "end"
    };
    const res = visitor.visit(invalidAnchor, { value: "abc", pos: 0 });
    expect(res).toEqual([]);
  });
});
