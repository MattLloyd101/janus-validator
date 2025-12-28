import { DomainCert } from "./DomainCert";
import type { DiscreteOrdered } from "@/domain/witnesses/DiscreteOrdered";

export class UnionCert<T> extends DomainCert<T> {
  readonly kind = "union";
  readonly left: DomainCert<T>;
  readonly right: DomainCert<T>;
  constructor(left: DomainCert<T>, right: DomainCert<T>, id?: string) {
    super(id);
    this.left = left;
    this.right = right;
  }

  hash(): string {
    return `union(${this.left.hash()}|${this.right.hash()})`;
  }

  withWitness(witness: DiscreteOrdered<T>): DomainCert<T> {
    return new UnionCert(this.left.withWitness(witness), this.right.withWitness(witness), this.id);
  }

  contains(value: T): boolean {
    return this.left.contains(value) || this.right.contains(value);
  }

  isEmpty(): boolean {
    return this.left.isEmpty() && this.right.isEmpty();
  }

  encapsulates(other: DomainCert<T>): boolean {
    if (this.equals(other)) return true;
    if (other.isEmpty()) return true;
    if (other instanceof UnionCert) {
      return this.encapsulates(other.left) && this.encapsulates(other.right);
    }
    // Conservative: both branches must cover the target.
    return this.left.encapsulates(other) && this.right.encapsulates(other);
  }
}

