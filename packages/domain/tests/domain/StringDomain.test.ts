import { StringDomain } from "@/domains/StringDomain";

describe("StringDomain", () => {
  it("enforces length bounds", () => {
    const domain = new StringDomain({ minLength: 1, maxLength: 3 });
    expect(domain.contains("a")).toBe(true);
    expect(domain.contains("abcd")).toBe(false);
  });

  it("throws on invalid bounds", () => {
    expect(() => new StringDomain({ minLength: 3, maxLength: 1 })).toThrow("Invalid string length bounds");
  });

  it("normalize clones bounds", () => {
    const domain = new StringDomain({ minLength: 1, maxLength: 2 });
    const norm = domain.normalize() as StringDomain;
    expect(norm.contains("ab")).toBe(true);
  });
});

