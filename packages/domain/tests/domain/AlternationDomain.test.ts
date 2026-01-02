import { AlternationDomain, normalizeAlternation } from "@/domains/AlternationDomain";
import { ContiguousDomain } from "@/domains/ContiguousDomain";
import { FiniteDomain } from "@/domains/FiniteDomain";

describe("AlternationDomain", () => {
  it("normalizes nested alternations and merges contiguous ranges", () => {
    const a = new ContiguousDomain(0, 2);
    const b = new ContiguousDomain(3, 5);
    const nested = new AlternationDomain<number>([new AlternationDomain([a, b])]);
    const normalized = normalizeAlternation([nested]);
    expect(normalized).toBeInstanceOf(ContiguousDomain);
    const range = normalized as ContiguousDomain<number>;
    expect(range.min).toBe(0);
    expect(range.max).toBe(5);
  });

  it("dedupes identical finite domains", () => {
    const normalized = normalizeAlternation<number>([
      new FiniteDomain([1, 2]),
      new FiniteDomain([1, 2]),
    ]) as AlternationDomain<number> | FiniteDomain<number>;
    if (normalized instanceof AlternationDomain) {
      expect(normalized.options.length).toBe(1);
    } else {
      expect(normalized.contains(1)).toBe(true);
    }
  });

  it("merges adjacent contiguous ranges", () => {
    const normalized = normalizeAlternation<number>([new ContiguousDomain(0, 1), new ContiguousDomain(2, 3)]) as ContiguousDomain<number>;
    expect(normalized.min).toBe(0);
    expect(normalized.max).toBe(3);
  });

  it("handles bigint adjacency", () => {
    const normalized = normalizeAlternation<bigint>([new ContiguousDomain(0n, 1n), new ContiguousDomain(2n, 3n)]) as ContiguousDomain<bigint>;
    expect(normalized.min).toBe(0n);
    expect(normalized.max).toBe(3n);
  });

  it("leaves non-overlapping ranges as alternation", () => {
    const normalized = normalizeAlternation<number>([new ContiguousDomain(0, 1), new ContiguousDomain(10, 11)]) as AlternationDomain<number>;
    expect(normalized).toBeInstanceOf(AlternationDomain);
    expect(normalized.options.length).toBe(2);
  });

  it("contains delegates to options", () => {
    const alt = new AlternationDomain<number>([new FiniteDomain([1]), new FiniteDomain([2])]);
    expect(alt.contains(2)).toBe(true);
    expect(alt.contains(3)).toBe(false);
  });

  it("merges overlapping ranges via overlap branch", () => {
    const normalized = normalizeAlternation<number>([new ContiguousDomain(0, 3), new ContiguousDomain(2, 4)]) as ContiguousDomain<number>;
    expect(normalized.min).toBe(0);
    expect(normalized.max).toBe(4);
  });

  it("returns single option directly during normalization", () => {
    const normalized = normalizeAlternation<number>([new ContiguousDomain(1, 2)]);
    expect(normalized).toBeInstanceOf(ContiguousDomain);
    expect((normalized as ContiguousDomain<number>).min).toBe(1);
  });

  it("merges bigint overlapping ranges", () => {
    const normalized = normalizeAlternation<bigint>([new ContiguousDomain(0n, 2n), new ContiguousDomain(2n, 5n)]) as ContiguousDomain<bigint>;
    expect(normalized.min).toBe(0n);
    expect(normalized.max).toBe(5n);
  });
});

