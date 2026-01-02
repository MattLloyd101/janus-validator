import { ContiguousDomain } from "@/domains/ContiguousDomain";
import { FiniteDomain } from "@/domains/FiniteDomain";
import { StructDomain } from "@/domains/StructDomain";
import { RegexDomain } from "@/domains/RegexDomain";
import { QuantifierDomain } from "@/domains/QuantifierDomain";
import { AlternationDomain } from "@/domains/AlternationDomain";
import { BytesDomain } from "@/domains/BytesDomain";
import { StringDomain } from "@/domains/StringDomain";
import { encapsulates } from "@/relations/encapsulates";

describe("encapsulates", () => {
  it("contiguous superset encapsulates subset", () => {
    const narrow = new ContiguousDomain(0, 5);
    const wide = new ContiguousDomain(0, 10);
    expect(encapsulates(wide, narrow).result).toBe("true");
    expect(encapsulates(narrow, wide).result).toBe("false");
  });

  it("struct encapsulation respects strictness", () => {
    const base = new StructDomain({ fields: { a: new FiniteDomain([1, 2]) }, strict: true });
    const relaxed = new StructDomain({ fields: { a: new FiniteDomain([1, 2]) }, strict: false });
    expect(encapsulates(relaxed, base).result).toBe("true");
    expect(encapsulates(base, relaxed).result).toBe("false");
  });

  it("struct propagates nested relation failures", () => {
    const sup = new StructDomain({ fields: { a: new ContiguousDomain(0, 5) }, strict: true });
    const sub = new StructDomain({ fields: { a: new ContiguousDomain(0, 10) }, strict: true });
    const res = encapsulates(sup, sub);
    expect(res.result).toBe("false");
    if (res.result === "false") expect(res.reason).toContain("range");
  });

  it("regex inclusion is unknown when patterns differ", () => {
    const a = new RegexDomain(/^abc$/);
    const b = new RegexDomain(/^abcd$/);
    expect(encapsulates(a, b).result).toBe("unknown");
  });

  it("regex inclusion is true for identical patterns", () => {
    const a = new RegexDomain(/^abc$/);
    const b = new RegexDomain(/^abc$/);
    expect(encapsulates(a, b).result).toBe("true");
  });

  it("quantifier fails when min is not covered", () => {
    const sup = new QuantifierDomain(new FiniteDomain([1]), { min: 2, max: 4 });
    const sub = new QuantifierDomain(new FiniteDomain([1]), { min: 1, max: 3 });
    const res = encapsulates(sup, sub);
    expect(res.result).toBe("false");
    if (res.result === "false") expect(res.reason).toContain("min length");
  });

  it("quantifier succeeds when ranges and inner are covered", () => {
    const sup = new QuantifierDomain(new FiniteDomain([1, 2]), { min: 1, max: 3 });
    const sub = new QuantifierDomain(new FiniteDomain([1]), { min: 1, max: 2 });
    const res = encapsulates(sup, sub);
    expect(res.result).toBe("true");
  });

  it("quantifier fails when max is not covered", () => {
    const sup = new QuantifierDomain(new FiniteDomain([1]), { min: 0, max: 1 });
    const sub = new QuantifierDomain(new FiniteDomain([1]), { min: 0, max: 3 });
    const res = encapsulates(sup, sub);
    expect(res.result).toBe("false");
    if (res.result === "false") expect(res.reason).toContain("max length");
  });

  it("string lengths encapsulate when sup is wider", () => {
    const sup = new StringDomain({ minLength: 0, maxLength: 10 });
    const sub = new StringDomain({ minLength: 1, maxLength: 5 });
    expect(encapsulates(sup, sub).result).toBe("true");
  });

  it("string lengths fail when sup is narrower", () => {
    const sup = new StringDomain({ minLength: 2, maxLength: 3 });
    const sub = new StringDomain({ minLength: 1, maxLength: 5 });
    expect(encapsulates(sup, sub).result).toBe("false");
  });

  it("struct reports missing field", () => {
    const sup = new StructDomain({ fields: { a: new FiniteDomain([1]) }, strict: true });
    const sub = new StructDomain({ fields: { a: new FiniteDomain([1]), b: new FiniteDomain([2]) }, strict: true });
    expect(encapsulates(sup, sub).result).toBe("false");
  });

  it("strict superset disallows extras", () => {
    const sup = new StructDomain({ fields: { a: new FiniteDomain([1]) }, strict: true });
    const sub = new StructDomain({ fields: { a: new FiniteDomain([1]) }, strict: false });
    const res = encapsulates(sup, sub);
    expect(res.result).toBe("false");
  });

  it("struct matches when strictness aligns", () => {
    const sup = new StructDomain({ fields: { a: new FiniteDomain([1]) }, strict: false });
    const sub = new StructDomain({ fields: { a: new FiniteDomain([1]) }, strict: false });
    expect(encapsulates(sup, sub).result).toBe("true");
  });

  it("alternation fully covers sub alternation", () => {
    const sup = new AlternationDomain<number>([new FiniteDomain([1]), new FiniteDomain([2])]);
    const sub = new AlternationDomain<number>([new FiniteDomain([1])]);
    expect(encapsulates(sup, sub).result).toBe("true");
  });

  it("alternation reports uncovered option", () => {
    const sup = new AlternationDomain<number>([new FiniteDomain([1]), new FiniteDomain([2])]);
    const sub = new AlternationDomain<number>([new FiniteDomain([3])]);
    expect(encapsulates(sup, sub).result).toBe("false");
  });

  it("contiguous vs finite reports outside value", () => {
    const sup = new ContiguousDomain(0, 5);
    const sub = new FiniteDomain([1, 10]);
    const res = encapsulates(sup, sub);
    expect(res.result).toBe("false");
    if (res.result === "false") expect(res.reason).toContain("outside range");
  });

  it("mismatched domain kinds return unknown", () => {
    const sup = new StringDomain({ minLength: 1, maxLength: 3 });
    const sub = new BytesDomain({ minLength: 1, maxLength: 3 });
    expect(encapsulates(sup, sub).result).toBe("unknown");
  });

  it("alternation covers non-alternation when option matches", () => {
    const sup = new AlternationDomain<number>([new FiniteDomain([1]), new FiniteDomain([2])]);
    const sub = new FiniteDomain([1]);
    expect(encapsulates(sup, sub).result).toBe("true");
  });

  it("alternation with non-matching sub returns false", () => {
    const sup = new AlternationDomain<number>([new FiniteDomain([1])]);
    const sub = new FiniteDomain([2]);
    expect(encapsulates(sup, sub).result).toBe("false");
  });

  it("quantifier inner mismatch propagates", () => {
    const sup = new QuantifierDomain(new FiniteDomain([1]), { min: 0, max: 2 });
    const sub = new QuantifierDomain(new FiniteDomain([2]), { min: 0, max: 2 });
    const res = encapsulates(sup, sub);
    expect(res.result).toBe("false");
  });

  it("contiguous encapsulates finite when all inside", () => {
    const sup = new ContiguousDomain(0, 5);
    const sub = new FiniteDomain([1, 2]);
    expect(encapsulates(sup, sub).result).toBe("true");
  });
});

