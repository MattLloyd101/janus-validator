import { BaseDomain, Domain } from "../Domain";
import { DomainType } from "../types";
import { ContiguousDomain } from "./ContiguousDomain";
import { FiniteDomain } from "./FiniteDomain";

/** Increment a number or bigint by 1 */
function increment(value: number | bigint): number | bigint {
  if (typeof value === "bigint") {
    return value + 1n;
  }
  return value + 1;
}

export class AlternationDomain<T> extends BaseDomain<T> {
  readonly kind = DomainType.ALTERNATION;
  readonly options: Domain<T>[];

  constructor(options: Domain<T>[]) {
    super();
    this.options = normalizeAlternationOptions(options);
  }

  contains(value: unknown): value is T {
    return this.options.some((opt) => opt.contains(value));
  }
}

function normalizeAlternationOptions<T>(options: Domain<T>[]): Domain<T>[] {
  const flattened: Domain<T>[] = [];
  const stack = [...options];
  while (stack.length > 0) {
    const opt = stack.pop() as Domain<T>;
    if (opt.kind === DomainType.ALTERNATION) {
      stack.push(...(opt as AlternationDomain<T>).options);
    } else {
      flattened.push(opt);
    }
  }

  // Contiguous domains hold numeric values (number or bigint)
  const contiguous: ContiguousDomain<number | bigint>[] = [];
  const others: Domain<T>[] = [];
  for (const opt of flattened) {
    if (opt.kind === DomainType.CONTIGUOUS) {
      // Safe cast: CONTIGUOUS domains are always ContiguousDomain<number | bigint>
      contiguous.push(opt as unknown as ContiguousDomain<number | bigint>);
    } else {
      others.push(opt);
    }
  }
  contiguous.sort((a, b) => (a.min < b.min ? -1 : a.min > b.min ? 1 : 0));
  const merged: ContiguousDomain<number | bigint>[] = [];
  for (const c of contiguous) {
    const last = merged[merged.length - 1];
    if (!last) {
      merged.push(c);
      continue;
    }
    const overlap = c.min <= last.max;
    const adjacent = c.min === increment(last.max);
    if (overlap || adjacent) {
      const max = c.max > last.max ? c.max : last.max;
      merged[merged.length - 1] = new ContiguousDomain(last.min, max);
    } else {
      merged.push(c);
    }
  }

  const uniqueFinite = new Map<string, FiniteDomain<unknown>>();
  const dedupedOthers: Domain<T>[] = [];
  for (const opt of others) {
    if (opt.kind === DomainType.FINITE) {
      const key = JSON.stringify((opt as FiniteDomain<unknown>).all);
      if (!uniqueFinite.has(key)) uniqueFinite.set(key, opt as FiniteDomain<unknown>);
    } else {
      dedupedOthers.push(opt);
    }
  }

  // Cast merged contiguous domains back to Domain<T> - safe because T includes the numeric types
  const normalized: Domain<T>[] = [
    ...(merged as unknown as Domain<T>[]),
    ...(Array.from(uniqueFinite.values()) as unknown as Domain<T>[]),
    ...dedupedOthers,
  ];
  return normalized;
}

export function normalizeAlternation<T>(options: Domain<T>[]): Domain<T> {
  const normalized = normalizeAlternationOptions(options);
  if (normalized.length === 1) return normalized[0];
  return new AlternationDomain(normalized);
}

