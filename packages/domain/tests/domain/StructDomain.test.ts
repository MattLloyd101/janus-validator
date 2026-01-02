import { StructDomain } from "@/domains/StructDomain";
import { FiniteDomain } from "@/domains/FiniteDomain";

describe("StructDomain", () => {
  it("honors strict flag", () => {
    const domain = new StructDomain({ fields: { a: new FiniteDomain([1]) }, strict: true });
    expect(domain.contains({ a: 1 })).toBe(true);
    expect(domain.contains({ a: 1, b: 2 })).toBe(false);
  });

  it("allows extra keys when non-strict", () => {
    const domain = new StructDomain({ fields: { a: new FiniteDomain([1]) }, strict: false });
    expect(domain.contains({ a: 1, b: 2 })).toBe(true);
  });

  it("fails when required field is missing", () => {
    const domain = new StructDomain({ fields: { a: new FiniteDomain([1]) }, strict: false });
    expect(domain.contains({})).toBe(false);
  });

  it("normalize normalizes nested domains", () => {
    const domain = new StructDomain({ fields: { a: new FiniteDomain([1]) }, strict: true });
    const norm = domain.normalize() as StructDomain<any>;
    expect(norm).not.toBe(domain);
    expect(norm.fields.a).not.toBe(domain.fields.a);
    expect(norm.contains({ a: 1 })).toBe(true);
  });

  it("rejects non-object inputs", () => {
    const domain = new StructDomain({ fields: { a: new FiniteDomain([1]) }, strict: true });
    expect(domain.contains(null as any)).toBe(false);
    expect(domain.contains(123 as any)).toBe(false);
  });

  it("rejects when inner domain fails", () => {
    const domain = new StructDomain({ fields: { a: new FiniteDomain([1]) }, strict: true });
    expect(domain.contains({ a: 2 })).toBe(false);
  });
});
