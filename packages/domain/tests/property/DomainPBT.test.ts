import { fc, pbt, pbtConfig } from "./pbt";
import { ContiguousDomain } from "@/domains/ContiguousDomain";
import { FiniteDomain } from "@/domains/FiniteDomain";
import { AlternationDomain } from "@/domains/AlternationDomain";
import { QuantifierDomain } from "@/domains/QuantifierDomain";
import { StringDomain } from "@/domains/StringDomain";
import { union, intersect } from "@/set/operations";
import { encapsulates } from "@/relations/encapsulates";

describe("Property-based invariants for domains", () => {
  it("ContiguousDomain contains iff value is within [min,max]", () =>
    pbt(
      fc.property(
        fc.integer({ min: -1_000_000, max: 1_000_000 }),
        fc.integer({ min: -1_000_000, max: 1_000_000 }),
        fc.integer({ min: -1_000_001, max: 1_000_001 }),
        (a, b, value) => {
          const min = Math.min(a, b);
          const max = Math.max(a, b);
          const domain = new ContiguousDomain(min, max);
          const expected = value >= min && value <= max;
          expect(domain.contains(value)).toBe(expected);
        }
      )
    ));

  if (pbtConfig.profile === "complete") {
    it("ContiguousDomain exhaustively covers small ranges", () =>
      pbt(
        fc.property(
          fc.integer({ min: -500, max: 500 }),
          fc.nat({ max: 50 }),
          (start, width) => {
            const min = start;
            const max = start + width;
            const domain = new ContiguousDomain(min, max);
            for (let v = min; v <= max; v++) {
              expect(domain.contains(v)).toBe(true);
            }
            expect(domain.contains(min - 1)).toBe(false);
            expect(domain.contains(max + 1)).toBe(false);
          }
        )
      ));
  }

  it("ContiguousDomain includes endpoints and excludes immediate neighbors", () =>
    pbt(
      fc.property(
        fc.integer({ min: -100_000, max: 100_000 }),
        fc.nat({ max: 10_000 }),
        (base, width) => {
          const min = base;
          const max = base + width;
          const domain = new ContiguousDomain(min, max);
          expect(domain.contains(min)).toBe(true);
          expect(domain.contains(max)).toBe(true);
          expect(domain.contains(min - 1)).toBe(false);
          expect(domain.contains(max + 1)).toBe(false);
        }
      )
    ));

  it("FiniteDomain contains iff value is a member of the set", () =>
    pbt(
      fc.property(
        fc.array(fc.integer({ min: -500, max: 500 }), { minLength: 0, maxLength: 30 }),
        fc.integer({ min: -600, max: 600 }),
        (values, candidate) => {
          const domain = new FiniteDomain(values);
          expect(domain.contains(candidate)).toBe(values.includes(candidate));
        }
      )
    ));

  it("AlternationDomain matches the union of option domains", () =>
    pbt(
      fc.property(
        fc.integer({ min: -500, max: 500 }),
        fc.integer({ min: -500, max: 500 }),
        fc.integer({ min: -500, max: 500 }),
        fc.integer({ min: -500, max: 500 }),
        fc.integer({ min: -600, max: 600 }),
        (a1, b1, a2, b2, value) => {
          const [min1, max1] = a1 <= b1 ? [a1, b1] : [b1, a1];
          const [min2, max2] = a2 <= b2 ? [a2, b2] : [b2, a2];
          const d1 = new ContiguousDomain(min1, max1);
          const d2 = new ContiguousDomain(min2, max2);
          const alt = new AlternationDomain([d1, d2]);
          const expected = d1.contains(value) || d2.contains(value);
          expect(alt.contains(value)).toBe(expected);
        }
      )
    ));

  it("QuantifierDomain enforces length bounds and inner membership", () =>
    pbt(
      fc.property(
        fc.nat({ max: 12 }),
        fc.option(fc.nat({ max: 16 }), { nil: undefined }),
        fc.array(fc.oneof(fc.constant(1), fc.constant(2)), { maxLength: 24 }),
        (min, optMax, items) => {
          const max = optMax === undefined ? undefined : Math.max(min, optMax);
          const domain = new QuantifierDomain(new FiniteDomain([1]), { min, max });
          const expectedLength = items.length >= min && (max === undefined || items.length <= max);
          const expectedInner = items.every((v) => v === 1);
          expect(domain.contains(items)).toBe(expectedLength && expectedInner);
        }
      )
    ));

  it("Set operations align with union/intersection semantics for contiguous domains", () =>
    pbt(
      fc.property(
        fc.integer({ min: -5_000, max: 5_000 }),
        fc.integer({ min: -5_000, max: 5_000 }),
        fc.integer({ min: -5_000, max: 5_000 }),
        fc.integer({ min: -5_000, max: 5_000 }),
        fc.integer({ min: -6_000, max: 6_000 }),
        (a1, b1, a2, b2, value) => {
          const [min1, max1] = a1 <= b1 ? [a1, b1] : [b1, a1];
          const [min2, max2] = a2 <= b2 ? [a2, b2] : [b2, a2];
          const d1 = new ContiguousDomain(min1, max1);
          const d2 = new ContiguousDomain(min2, max2);

          const unionDomain = union(d1, d2);
          const intersectDomain = intersect(d1, d2);

          expect(unionDomain.contains(value)).toBe(d1.contains(value) || d2.contains(value));

          const overlapMin = Math.max(min1, min2);
          const overlapMax = Math.min(max1, max2);
          const expectedIntersect = overlapMin <= overlapMax && value >= overlapMin && value <= overlapMax;
          expect(intersectDomain.contains(value)).toBe(expectedIntersect);
        }
      )
    ));

  it("encapsulates is reflexive and covers contiguous subsets", () =>
    pbt(
      fc.property(
        fc.integer({ min: -1_000, max: 1_000 }),
        fc.integer({ min: -1_000, max: 1_000 }),
        fc.integer({ min: -1_000, max: 1_000 }),
        fc.integer({ min: -1_000, max: 1_000 }),
        (a1, b1, a2, b2) => {
          const [min1, max1] = a1 <= b1 ? [a1, b1] : [b1, a1];
          const [min2, max2] = a2 <= b2 ? [a2, b2] : [b2, a2];
          const sup = new ContiguousDomain(Math.min(min1, min2), Math.max(max1, max2));
          const sub = new ContiguousDomain(min2, max2);

          expect(encapsulates(sub, sub).result).toBe("true");
          expect(encapsulates(sup, sub).result).toBe("true");
        }
      )
    ));

  it("StringDomain respects min/max length including extremes", () =>
    pbt(
      fc.property(
        fc.integer({ min: 0, max: 20 }),
        fc.integer({ min: 0, max: 20 }),
        fc.string({ maxLength: 30 }),
        (a, b, candidate) => {
          const min = Math.min(a, b);
          const max = Math.max(a, b, min); // ensure max >= min
          const domain = new StringDomain({ minLength: min, maxLength: max });
          const len = candidate.length;
          const expected = len >= min && len <= max;
          expect(domain.contains(candidate)).toBe(expected);
        }
      )
    ));
});

