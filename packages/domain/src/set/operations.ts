import { Domain } from "../Domain";
import { DomainType } from "../types";
import { ContiguousDomain } from "../domains/ContiguousDomain";
import { FiniteDomain } from "../domains/FiniteDomain";
import { AlternationDomain } from "../domains/AlternationDomain";

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
  const adjacent =
    typeof left.max === "bigint"
      ? left.max + (1n as any) === right.min || right.max + (1n as any) === left.min
      : (left.max as number) + 1 === (right.min as number) || (right.max as number) + 1 === (left.min as number);
  if (overlaps || adjacent) {
    const min = left.min < right.min ? left.min : right.min;
    const max = left.max > right.max ? left.max : right.max;
    return new ContiguousDomain(min, max);
  }
  return new AlternationDomain([left, right]).normalize();
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
    const beforeMax = (typeof b.min === "bigint" ? (b.min - (1n as any)) : ((b.min as number) - 1)) as T;
    parts.push(new ContiguousDomain(a.min, beforeMax));
  }
  if (b.max < a.max) {
    const afterMin = (typeof b.max === "bigint" ? (b.max + (1n as any)) : ((b.max as number) + 1)) as T;
    parts.push(new ContiguousDomain(afterMin, a.max));
  }
  if (parts.length === 1) return parts[0];
  return new AlternationDomain(parts).normalize();
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

export function union(a: Domain<any>, b: Domain<any>): Domain<any> {
  if (a.kind === DomainType.CONTIGUOUS && b.kind === DomainType.CONTIGUOUS) {
    return unionContiguous(a as ContiguousDomain<any>, b as ContiguousDomain<any>).normalize();
  }
  if (a.kind === DomainType.FINITE && b.kind === DomainType.FINITE) {
    return unionFinite(a as FiniteDomain<any>, b as FiniteDomain<any>).normalize();
  }
  return new AlternationDomain([a, b]).normalize();
}

export function intersect(a: Domain<any>, b: Domain<any>): Domain<any> {
  if (a.kind === DomainType.CONTIGUOUS && b.kind === DomainType.CONTIGUOUS) {
    return intersectContiguous(a as ContiguousDomain<any>, b as ContiguousDomain<any>).normalize();
  }
  if (a.kind === DomainType.FINITE && b.kind === DomainType.FINITE) {
    return intersectFinite(a as FiniteDomain<any>, b as FiniteDomain<any>).normalize();
  }
  if (a.kind === DomainType.ALTERNATION) {
    const options = (a as AlternationDomain<any>).options.map((opt) => intersect(opt, b));
    return new AlternationDomain(options).normalize();
  }
  if (b.kind === DomainType.ALTERNATION) {
    return intersect(b, a);
  }
  return new FiniteDomain([]); // exact-first: unsupported combo → empty set instead of approximation
}

export function subtract(a: Domain<any>, b: Domain<any>): Domain<any> {
  if (a.kind === DomainType.CONTIGUOUS && b.kind === DomainType.CONTIGUOUS) {
    return subtractContiguous(a as ContiguousDomain<any>, b as ContiguousDomain<any>).normalize();
  }
  if (a.kind === DomainType.FINITE && b.kind === DomainType.FINITE) {
    return subtractFinite(a as FiniteDomain<any>, b as FiniteDomain<any>).normalize();
  }
  if (a.kind === DomainType.ALTERNATION) {
    const options = (a as AlternationDomain<any>).options.map((opt) => subtract(opt, b));
    return new AlternationDomain(options).normalize();
  }
  throw new Error("Unsupported subtract combination");
}

