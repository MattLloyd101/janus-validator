import { SequenceDomain } from "@/domains/SequenceDomain";
import { FiniteDomain } from "@/domains/FiniteDomain";

describe("SequenceDomain", () => {
  it("validates tuples by part", () => {
    const seq = new SequenceDomain([new FiniteDomain([1]), new FiniteDomain(["x"])]);
    expect(seq.contains([1, "x"])).toBe(true);
    expect(seq.contains([2, "x"])).toBe(false);
  });

  it("fails when length mismatches", () => {
    const seq = new SequenceDomain([new FiniteDomain([1])]);
    expect(seq.contains([])).toBe(false);
  });

  it("fails for non-array input", () => {
    const seq = new SequenceDomain([new FiniteDomain([1])]);
    expect(seq.contains("not-array" as any)).toBe(false);
  });
});

