import { RegexDomain } from "@/domains/RegexDomain";

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
    expect(domain.contains(123 as any)).toBe(false);
  });

  it("normalize recreates pattern", () => {
    const domain = new RegexDomain(/^abc$/);
    const norm = domain.normalize();
    expect(norm.contains("abc")).toBe(true);
  });

  it("throws on flags for portability", () => {
    expect(() => new RegexDomain(/abc/i)).toThrow(/Unsupported regex flags/);
  });
});
