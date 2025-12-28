import { DomainCert } from "./DomainCert";
import { ContiguousCert } from "./ContiguousCert";
import { FiniteCert } from "./FiniteCert";
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

  normalize(): DomainCert<T> {
    const parts = this.flattenUnion().map((c) => c.normalize()).filter((c) => !c.isEmpty());
    if (parts.length === 0) return UnionCert.empty<T>();
    const merged = ContiguousCert.mergeContiguous(parts);
    if (merged.length === 1) return merged[0];
    return UnionCert.buildUnionChain(merged);
  }

  private flattenUnion(): DomainCert<T>[] {
    const stack: DomainCert<T>[] = [];
    const push = (c: DomainCert<T>) => {
      if (c instanceof UnionCert) {
        push(c.left);
        push(c.right);
      } else {
        stack.push(c);
      }
    };
    push(this.left);
    push(this.right);
    return stack;
  }

  private static buildUnionChain<T>(parts: DomainCert<T>[]): DomainCert<T> {
    return parts.slice(1).reduce((acc, cur) => new UnionCert(acc, cur), parts[0]);
  }

  private static empty<T>(): DomainCert<T> {
    return new FiniteCert<T>([]);
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

