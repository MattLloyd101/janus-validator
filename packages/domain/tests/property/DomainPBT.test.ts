import { fc, pbt } from "./pbt";
import { ContiguousDomain } from "@/domains/ContiguousDomain";
import { FiniteDomain } from "@/domains/FiniteDomain";
import { AlternationDomain } from "@/domains/AlternationDomain";
import { QuantifierDomain } from "@/domains/QuantifierDomain";
import { union, intersect } from "@/set/operations";
import { encapsulates } from "@/relations/encapsulates";

describe("Property-based invariants for domains", () => {
  it("ContiguousDomain contains iff value is within [min,max]", () =>
    pbt(
      fc.property(
        fc.integer({ min: -1_000, max: 1_000 }),
        fc.integer({ min: -1_000, max: 1_000 }),
        fc.integer({ min: -1_100, max: 1_100 }),
        (a, b, value) => {
          const min = Math.min(a, b);
          const max = Math.max(a, b);
          const domain = new ContiguousDomain(min, max);
          const expected = value >= min && value <= max;
          expect(domain.contains(value)).toBe(expected);
        }
      )
    ));

  it("FiniteDomain contains iff value is a member of the set", () =>
    pbt(
      fc.property(
        fc.array(fc.integer({ min: -20, max: 20 }), { minLength: 1, maxLength: 10 }),
        fc.integer({ min: -25, max: 25 }),
        (values, candidate) => {
          const domain = new FiniteDomain(values);
          expect(domain.contains(candidate)).toBe(values.includes(candidate));
        }
      )
    ));

  it("AlternationDomain matches the union of option domains", () =>
    pbt(
      fc.property(
        fc.integer({ min: -50, max: 50 }),
        fc.integer({ min: -50, max: 50 }),
        fc.integer({ min: -50, max: 50 }),
        fc.integer({ min: -50, max: 50 }),
        fc.integer({ min: -60, max: 60 }),
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
        fc.nat({ max: 5 }),
        fc.option(fc.nat({ max: 8 }), { nil: undefined }),
        fc.array(fc.oneof(fc.constant(1), fc.constant(2)), { maxLength: 10 }),
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
        fc.integer({ min: -30, max: 30 }),
        fc.integer({ min: -30, max: 30 }),
        fc.integer({ min: -30, max: 30 }),
        fc.integer({ min: -30, max: 30 }),
        fc.integer({ min: -40, max: 40 }),
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
        fc.integer({ min: -50, max: 50 }),
        fc.integer({ min: -50, max: 50 }),
        fc.integer({ min: -50, max: 50 }),
        fc.integer({ min: -50, max: 50 }),
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
});

