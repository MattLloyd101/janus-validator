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

  it("allows empty string when minLength is zero", () => {
    const domain = new StringDomain({ minLength: 0, maxLength: 2 });
    expect(domain.contains("")).toBe(true);
    expect(domain.contains("abc")).toBe(false);
  });
});

