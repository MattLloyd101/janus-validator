import { DomainCert } from "./DomainCert";
import type { SerializedIntersectCert } from "./Serialize";
import { ContiguousCert } from "./ContiguousCert";
import type { DiscreteOrdered } from "@/domain/witnesses/DiscreteOrdered";

export class IntersectCert<T> extends DomainCert<T> {
  readonly kind = "intersect";
  readonly left: DomainCert<T>;
  readonly right: DomainCert<T>;
  constructor(left: DomainCert<T>, right: DomainCert<T>, id?: string) {
    super(id);
    this.left = left;
    this.right = right;
  }

  hash(): string {
    return `intersect(${this.left.hash()}&${this.right.hash()})`;
  }

  withWitness(witness: DiscreteOrdered<T>): DomainCert<T> {
    return new IntersectCert(this.left.withWitness(witness), this.right.withWitness(witness), this.id);
  }

  static intersectRanges<T>(a: ContiguousCert<T>, b: ContiguousCert<T>): ContiguousCert<T> | null {
    const witness = a.witness;
    const min = witness.compare(a.min, b.min) >= 0 ? a.min : b.min;
    const max = witness.compare(a.max, b.max) <= 0 ? a.max : b.max;
    if (witness.compare(min, max) > 0) return null;
    return new ContiguousCert(min, max, witness);
  }

  contains(value: T): boolean {
    return this.left.contains(value) && this.right.contains(value);
  }

  isEmpty(): boolean {
    return this.left.isEmpty() || this.right.isEmpty();
  }

  encapsulates(other: DomainCert<T>): boolean {
    if (this.equals(other)) return true;
    if (other.isEmpty()) return true;
    if (other instanceof IntersectCert) {
      return this.encapsulates(other.left) && this.encapsulates(other.right);
    }
    // Conservative: intersection covers X only if both parts cover X.
    return this.left.encapsulates(other) && this.right.encapsulates(other);
  }

  serialize(): SerializedIntersectCert<T> {
    return {
      kind: "intersect",
      id: this.id,
      left: this.left.serialize(),
      right: this.right.serialize()
    };
  }
}

