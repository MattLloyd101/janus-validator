import { TransformDomain } from "@/domains/TransformDomain";
import { StringDomain } from "@/domains/StringDomain";
import { ContiguousDomain } from "@/domains/ContiguousDomain";
import { FiniteDomain } from "@/domains/FiniteDomain";
import { DomainType } from "@/types";

describe("TransformDomain", () => {
  describe("constructor", () => {
    it("should create a domain with inner domain and transform", () => {
      const inner = new StringDomain({ minLength: 1, maxLength: 50 });
      const domain = new TransformDomain<string, string, typeof inner>(inner, (s: string) => s.toUpperCase());

      expect(domain.inner).toBe(inner);
      expect(domain.transform).toBeDefined();
      expect(typeof domain.transform).toBe("function");
    });

    it("should have TRANSFORM kind", () => {
      const inner = new StringDomain({ minLength: 1, maxLength: 50 });
      const domain = new TransformDomain<string, string, typeof inner>(inner, (s: string) => s.toUpperCase());

      expect(domain.kind).toBe(DomainType.TRANSFORM);
    });
  });

  describe("transform function", () => {
    it("should store the provided transform function", () => {
      const transformFn = (s: string) => s.trim();
      const inner = new StringDomain({ minLength: 1, maxLength: 50 });
      const domain = new TransformDomain<string, string, typeof inner>(inner, transformFn);

      expect(domain.transform).toBe(transformFn);
    });

    it("should work with identity transform", () => {
      const inner = new StringDomain({ minLength: 1, maxLength: 50 });
      const domain = new TransformDomain<string, string, typeof inner>(inner, (s: string) => s);

      expect(domain.transform("hello")).toBe("hello");
    });

    it("should work with type-changing transform", () => {
      const inner = new StringDomain({ minLength: 1, maxLength: 50 });
      const domain = new TransformDomain<string, number, typeof inner>(inner, (s: string) => s.length);

      expect(domain.transform("hello")).toBe(5);
    });

    it("should work with object-returning transform", () => {
      const inner = new StringDomain({ minLength: 1, maxLength: 50 });
      const domain = new TransformDomain<string, { value: string; length: number }, typeof inner>(
        inner,
        (s: string) => ({ value: s, length: s.length })
      );

      expect(domain.transform("hi")).toEqual({ value: "hi", length: 2 });
    });
  });

  describe("contains", () => {
    it("should return true for any value (conservative approximation)", () => {
      const inner = new StringDomain({ minLength: 1, maxLength: 50 });
      const domain = new TransformDomain<string, string, typeof inner>(inner, (s: string) => s.toUpperCase());

      // TransformDomain.contains() always returns true because
      // we cannot invert the transform to check membership
      expect(domain.contains("HELLO")).toBe(true);
      expect(domain.contains("hello")).toBe(true);
      expect(domain.contains(123)).toBe(true);
      expect(domain.contains(null)).toBe(true);
      expect(domain.contains(undefined)).toBe(true);
      expect(domain.contains({ foo: "bar" })).toBe(true);
    });
  });

  describe("with different inner domains", () => {
    it("should work with ContiguousDomain", () => {
      const inner = new ContiguousDomain(0, 100);
      const domain = new TransformDomain<number, number, typeof inner>(inner, (n: number) => n * 2);

      expect(domain.inner).toBe(inner);
      expect(domain.transform(21)).toBe(42);
    });

    it("should work with FiniteDomain", () => {
      const inner = new FiniteDomain(["a", "b", "c"]);
      const domain = new TransformDomain<string, string, typeof inner>(inner, (s: string) => s.toUpperCase());

      expect(domain.inner).toBe(inner);
      expect(domain.transform("a")).toBe("A");
    });

    it("should support nested TransformDomains", () => {
      const inner = new StringDomain({ minLength: 1, maxLength: 50 });
      const trimDomain = new TransformDomain<string, string, typeof inner>(inner, (s: string) => s.trim());
      const upperDomain = new TransformDomain<string, string, typeof trimDomain>(trimDomain, (s: string) => s.toUpperCase());

      expect(upperDomain.inner).toBe(trimDomain);
      expect(upperDomain.transform("  hello  ")).toBe("  HELLO  "); // Only applies toUpperCase
      // To get full chain, you'd call trimDomain.transform first
      expect(upperDomain.transform(trimDomain.transform("  hello  "))).toBe("HELLO");
    });
  });
});
