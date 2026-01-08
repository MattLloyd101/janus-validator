import { Domain } from "../Domain";
import { DomainType } from "../types";
import { ContiguousDomain } from "../domains/ContiguousDomain";
import { FiniteDomain } from "../domains/FiniteDomain";
import { AlternationDomain, normalizeAlternation } from "../domains/AlternationDomain";

/**
 * Increment a number or bigint by 1, preserving the type.
 */
function increment<T extends number | bigint>(value: T): T {
  if (typeof value === "bigint") {
    return (value + 1n) as T;
  }
  return ((value as number) + 1) as T;
}

/**
 * Decrement a number or bigint by 1, preserving the type.
 */
function decrement<T extends number | bigint>(value: T): T {
  if (typeof value === "bigint") {
    return (value - 1n) as T;
  }
  return ((value as number) - 1) as T;
}

function intersectContiguous<T extends number | bigint>(
  left: ContiguousDomain<T>,
  right: ContiguousDomain<T>
): Domain<T> {
  const min = left.min > right.min ? left.min : right.min;
  const max = left.max < right.max ? left.max : right.max;
  if (min > max) {
    return new FiniteDomain<T>([]);
  }
  return new ContiguousDomain(min, max);
}

function unionContiguous<T extends number | bigint>(
  left: ContiguousDomain<T>,
  right: ContiguousDomain<T>
): Domain<T> {
  const overlaps = !(left.max < right.min || right.max < left.min);
  const adjacent = increment(left.max) === right.min || increment(right.max) === left.min;
  if (overlaps || adjacent) {
    const min = left.min < right.min ? left.min : right.min;
    const max = left.max > right.max ? left.max : right.max;
    return new ContiguousDomain(min, max);
  }
  return normalizeAlternation([left, right]);
}

function subtractContiguous<T extends number | bigint>(
  a: ContiguousDomain<T>,
  b: ContiguousDomain<T>
): Domain<T> {
  if (b.max < a.min || b.min > a.max) return a;
  if (b.min <= a.min && b.max >= a.max) {
    return new FiniteDomain<T>([]);
  }
  const parts: ContiguousDomain<T>[] = [];
  if (b.min > a.min) {
    parts.push(new ContiguousDomain(a.min, decrement(b.min)));
  }
  if (b.max < a.max) {
    parts.push(new ContiguousDomain(increment(b.max), a.max));
  }
  if (parts.length === 1) return parts[0];
  return normalizeAlternation(parts);
}

function intersectFinite<T>(a: FiniteDomain<T>, b: FiniteDomain<T>): Domain<T> {
  const result: T[] = [];
  for (const v of a.all) {
    if (b.contains(v)) result.push(v);
  }
  return new FiniteDomain(result);
}

function unionFinite<T>(a: FiniteDomain<T>, b: FiniteDomain<T>): Domain<T> {
  return new FiniteDomain([...a.all, ...b.all]);
}

function subtractFinite<T>(a: FiniteDomain<T>, b: FiniteDomain<T>): Domain<T> {
  const remaining = a.all.filter((v) => !b.contains(v));
  return new FiniteDomain(remaining);
}

export function union<T>(a: Domain<T>, b: Domain<T>): Domain<T> {
  if (a.kind === DomainType.CONTIGUOUS && b.kind === DomainType.CONTIGUOUS) {
    return unionContiguous(
      a as ContiguousDomain<T & (number | bigint)>,
      b as ContiguousDomain<T & (number | bigint)>
    ) as Domain<T>;
  }
  if (a.kind === DomainType.FINITE && b.kind === DomainType.FINITE) {
    return unionFinite(a as FiniteDomain<T>, b as FiniteDomain<T>);
  }
  return normalizeAlternation([a, b]);
}

export function intersect<T>(a: Domain<T>, b: Domain<T>): Domain<T> {
  if (a.kind === DomainType.CONTIGUOUS && b.kind === DomainType.CONTIGUOUS) {
    return intersectContiguous(
      a as ContiguousDomain<T & (number | bigint)>,
      b as ContiguousDomain<T & (number | bigint)>
    ) as Domain<T>;
  }
  if (a.kind === DomainType.FINITE && b.kind === DomainType.FINITE) {
    return intersectFinite(a as FiniteDomain<T>, b as FiniteDomain<T>);
  }
  if (a.kind === DomainType.ALTERNATION) {
    const options = (a as AlternationDomain<T>).options.map((opt) => intersect(opt, b));
    return normalizeAlternation(options);
  }
  if (b.kind === DomainType.ALTERNATION) {
    return intersect(b, a);
  }
  return new FiniteDomain<T>([]); // exact-first: unsupported combo → empty set instead of approximation
}

export function subtract<T>(a: Domain<T>, b: Domain<T>): Domain<T> {
  if (a.kind === DomainType.CONTIGUOUS && b.kind === DomainType.CONTIGUOUS) {
    return subtractContiguous(
      a as ContiguousDomain<T & (number | bigint)>,
      b as ContiguousDomain<T & (number | bigint)>
    ) as Domain<T>;
  }
  if (a.kind === DomainType.FINITE && b.kind === DomainType.FINITE) {
    return subtractFinite(a as FiniteDomain<T>, b as FiniteDomain<T>);
  }
  if (a.kind === DomainType.ALTERNATION) {
    const options = (a as AlternationDomain<T>).options.map((opt) => subtract(opt, b));
    return normalizeAlternation(options);
  }
  throw new Error("Unsupported subtract combination");
}

