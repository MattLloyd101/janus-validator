import { BaseDomain } from "@/Domain";
import { DomainType } from "@/types";

class DummyDomain extends BaseDomain<number> {
  readonly kind = DomainType.FINITE;
  contains(value: unknown): value is number {
    return typeof value === "number";
  }
}

describe("BaseDomain", () => {
  it("exposes contains without public normalize", () => {
    const d = new DummyDomain();
    expect(d.contains(1)).toBe(true);
    expect(d.contains("nope")).toBe(false);
    // normalize is protected; not enumerable on the instance
    expect(Object.keys(d)).not.toContain("normalize");
  });
});

