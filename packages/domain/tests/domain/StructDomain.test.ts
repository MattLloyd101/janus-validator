import { StructDomain } from "@/domains/StructDomain";
import { FiniteDomain } from "@/domains/FiniteDomain";
import { StringDomain } from "@/domains/StringDomain";

describe("StructDomain", () => {
  it("validates objects with correct fields", () => {
    const domain = new StructDomain<{ name: string; age: number }>({
      fields: {
        name: new StringDomain({ minLength: 1, maxLength: 50 }),
        age: new FiniteDomain([25, 30, 35]),
      },
      strict: false,
    });
    expect(domain.contains({ name: "Alice", age: 30 })).toBe(true);
    expect(domain.contains({ name: "Bob", age: 40 })).toBe(false);
  });

  it("rejects non-object values", () => {
    const domain = new StructDomain<{ name: string }>({
      fields: { name: new StringDomain({ minLength: 1, maxLength: 50 }) },
      strict: false,
    });
    // Testing defensive behavior
    expect(domain.contains(null)).toBe(false);
    expect(domain.contains(123)).toBe(false);
    expect(domain.contains([1, 2, 3])).toBe(false);
  });

  it("enforces strict mode", () => {
    const strictDomain = new StructDomain<{ name: string }>({
      fields: { name: new StringDomain({ minLength: 1, maxLength: 50 }) },
      strict: true,
    });
    expect(strictDomain.contains({ name: "Alice" })).toBe(true);
    expect(strictDomain.contains({ name: "Alice", extra: 123 })).toBe(false);
  });

  it("rejects objects with missing fields", () => {
    const domain = new StructDomain<{ name: string; age: number }>({
      fields: {
        name: new StringDomain({ minLength: 1, maxLength: 50 }),
        age: new FiniteDomain([25, 30]),
      },
      strict: false,
    });
    // Missing 'age' field
    expect(domain.contains({ name: "Alice" })).toBe(false);
    // Missing 'name' field
    expect(domain.contains({ age: 25 })).toBe(false);
  });
});
