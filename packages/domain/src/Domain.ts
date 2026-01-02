import { DomainType } from "./types";

export interface Domain<T = unknown> {
  readonly kind: DomainType;
  contains(value: unknown): value is T;
  normalize(): Domain<T>;
}

export abstract class BaseDomain<T> implements Domain<T> {
  abstract readonly kind: DomainType;
  abstract contains(value: unknown): value is T;
  normalize(): Domain<T> {
    return this;
  }
}

