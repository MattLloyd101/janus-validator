import { DomainCert } from "./DomainCert";
import type { DiscreteOrdered } from "@/domain/witnesses/DiscreteOrdered";

export class FiniteCert<T> extends DomainCert<T> {
  readonly kind = "finite";
  readonly values: readonly T[];
  constructor(values: readonly T[], id?: string) {
    super(id);
    this.values = values;
  }

  hash(): string {
    return `finite:${this.renderValues(this.values)}`;
  }

  withWitness(_witness: DiscreteOrdered<T>): DomainCert<T> {
    return this;
  }

  contains(value: T): boolean {
    return this.values.some((v) => Object.is(v, value));
  }

  isEmpty(): boolean {
    return this.values.length === 0;
  }

  encapsulates(other: DomainCert<T>): boolean {
    if (this.isEmpty()) return other.isEmpty();
    if (other instanceof FiniteCert) {
      return other.values.every((v) => this.values.some((sv) => Object.is(sv, v)));
    }
    return false;
  }
}

