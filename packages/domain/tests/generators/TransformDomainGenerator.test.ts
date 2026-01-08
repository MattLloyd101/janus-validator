import { TransformDomainGenerator } from "@/generators/TransformDomainGenerator";
import { DomainGeneratorStrategyRegistry } from "@/generators/DomainGeneratorStrategyRegistry";
import { TransformDomain } from "@/domains/TransformDomain";
import { StringDomain } from "@/domains/StringDomain";
import { ContiguousDomain } from "@/domains/ContiguousDomain";
import { FiniteDomain } from "@/domains/FiniteDomain";
import { RNG } from "@/generators/RNG";

describe("TransformDomainGenerator", () => {
  let registry: DomainGeneratorStrategyRegistry;
  let rng: RNG;

  beforeEach(() => {
    registry = new DomainGeneratorStrategyRegistry();
    rng = { random: Math.random };
  });

  describe("generate", () => {
    it("should generate from inner domain and apply transform", () => {
      const inner = new StringDomain({ minLength: 5, maxLength: 10 });
      const domain = new TransformDomain<string, string, typeof inner>(inner, (s: string) => s.toUpperCase());
      const generator = new TransformDomainGenerator<string, string>(registry);

      for (let i = 0; i < 20; i++) {
        const value = generator.generate(domain, rng);
        expect(typeof value).toBe("string");
        expect(value).toBe(value.toUpperCase());
        expect(value.length).toBeGreaterThanOrEqual(5);
        expect(value.length).toBeLessThanOrEqual(10);
      }
    });

    it("should handle type-changing transforms", () => {
      const inner = new StringDomain({ minLength: 1, maxLength: 10 });
      const domain = new TransformDomain<string, number, typeof inner>(inner, (s: string) => s.length);
      const generator = new TransformDomainGenerator<string, number>(registry);

      for (let i = 0; i < 20; i++) {
        const value = generator.generate(domain, rng);
        expect(typeof value).toBe("number");
        expect(value).toBeGreaterThanOrEqual(1);
        expect(value).toBeLessThanOrEqual(10);
      }
    });

    it("should work with ContiguousDomain", () => {
      const inner = new ContiguousDomain(0, 100);
      const domain = new TransformDomain<number, number, typeof inner>(inner, (n: number) => n * 2);
      const generator = new TransformDomainGenerator<number, number>(registry);

      for (let i = 0; i < 20; i++) {
        const value = generator.generate(domain, rng);
        expect(typeof value).toBe("number");
        expect(value).toBeGreaterThanOrEqual(0);
        expect(value).toBeLessThanOrEqual(200);
      }
    });

    it("should work with FiniteDomain", () => {
      const inner = new FiniteDomain(["alice", "bob", "charlie"]);
      const domain = new TransformDomain<string, string, typeof inner>(inner, (s: string) => s.toUpperCase());
      const generator = new TransformDomainGenerator<string, string>(registry);

      const generated = new Set<string>();
      for (let i = 0; i < 50; i++) {
        const value = generator.generate(domain, rng);
        generated.add(value);
      }

      // Should only generate uppercase versions
      expect(generated.has("ALICE") || generated.has("BOB") || generated.has("CHARLIE")).toBe(true);
      expect(generated.has("alice")).toBe(false);
    });

    it("should handle object-returning transforms", () => {
      const inner = new StringDomain({ minLength: 1, maxLength: 20 });
      type Result = { original: string; length: number; upper: string };
      const domain = new TransformDomain<string, Result, typeof inner>(inner, (s: string) => ({
        original: s,
        length: s.length,
        upper: s.toUpperCase(),
      }));
      const generator = new TransformDomainGenerator<string, Result>(registry);

      for (let i = 0; i < 10; i++) {
        const value = generator.generate(domain, rng);
        expect(typeof value).toBe("object");
        expect(value).toHaveProperty("original");
        expect(value).toHaveProperty("length");
        expect(value).toHaveProperty("upper");
        expect(value.length).toBe(value.original.length);
        expect(value.upper).toBe(value.original.toUpperCase());
      }
    });

    it("should handle nested TransformDomains", () => {
      const inner = new StringDomain({ minLength: 1, maxLength: 20 });
      const trimDomain = new TransformDomain<string, string, typeof inner>(inner, (s: string) => s.trim());
      const upperDomain = new TransformDomain<string, string, typeof trimDomain>(trimDomain, (s: string) => s.toUpperCase());
      const generator = new TransformDomainGenerator<string, string>(registry);

      for (let i = 0; i < 20; i++) {
        const value = generator.generate(upperDomain, rng);
        expect(typeof value).toBe("string");
        // Should be uppercase (and trimmed from the intermediate step)
        expect(value).toBe(value.toUpperCase());
      }
    });
  });

  describe("via registry", () => {
    it("should be registered in the registry by default", () => {
      const inner = new StringDomain({ minLength: 1, maxLength: 10 });
      const domain = new TransformDomain<string, string, typeof inner>(inner, (s: string) => s.toLowerCase());

      const value = registry.generate(domain, rng);
      expect(typeof value).toBe("string");
      expect(value).toBe((value as string).toLowerCase());
    });
  });
});
