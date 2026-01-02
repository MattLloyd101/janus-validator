import { BaseDomain } from "@/Domain";
import { DomainType } from "@/types";

class DummyDomain extends BaseDomain<number> {
  readonly kind = DomainType.FINITE;
  contains(value: unknown): value is number {
    return typeof value === "number";
  }
}

describe("BaseDomain", () => {
  it("normalize returns self by default", () => {
    const d = new DummyDomain();
    expect(d.normalize()).toBeInstanceOf(DummyDomain);
    expect(d.normalize().contains(1)).toBe(true);
  });
});

