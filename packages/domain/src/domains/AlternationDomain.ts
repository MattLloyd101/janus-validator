import { BaseDomain, Domain } from "../Domain";
import { DomainType } from "../types";
import { ContiguousDomain } from "./ContiguousDomain";
import { FiniteDomain } from "./FiniteDomain";

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

  const contiguous: ContiguousDomain<any>[] = [];
  const others: Domain<T>[] = [];
  for (const opt of flattened) {
    if (opt.kind === DomainType.CONTIGUOUS) contiguous.push(opt as ContiguousDomain<any>);
    else others.push(opt);
  }
  contiguous.sort((a, b) => (a.min < b.min ? -1 : a.min > b.min ? 1 : 0));
  const merged: ContiguousDomain<any>[] = [];
  for (const c of contiguous) {
    const last = merged[merged.length - 1];
    if (!last) {
      merged.push(c);
      continue;
    }
    const isBigInt = typeof last.max === "bigint";
    const overlap = c.min <= last.max;
    const adjacent = isBigInt ? (c.min as any) === (last.max as any) + 1n : (c.min as any) === (last.max as any) + 1;
    if (overlap || adjacent) {
      const max = c.max > last.max ? c.max : last.max;
      merged[merged.length - 1] = new ContiguousDomain(last.min, max);
    } else {
      merged.push(c);
    }
  }

  const uniqueFinite = new Map<string, FiniteDomain<any>>();
  const dedupedOthers: Domain<T>[] = [];
  for (const opt of others) {
    if (opt.kind === DomainType.FINITE) {
      const key = JSON.stringify((opt as FiniteDomain<any>).all);
      if (!uniqueFinite.has(key)) uniqueFinite.set(key, opt as FiniteDomain<any>);
    } else {
      dedupedOthers.push(opt);
    }
  }

  const normalized: Domain<T>[] = [...merged, ...uniqueFinite.values(), ...dedupedOthers];
  return normalized;
}

export function normalizeAlternation<T>(options: Domain<T>[]): Domain<T> {
  const normalized = normalizeAlternationOptions(options);
  if (normalized.length === 1) return normalized[0];
  return new AlternationDomain(normalized);
}

