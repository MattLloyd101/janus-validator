import { DomainCert } from "./DomainCert";
import { ContiguousCert } from "./ContiguousCert";
import { FiniteCert } from "./FiniteCert";
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

  normalize(): DomainCert<T> {
    const parts = this.flattenIntersect().map((c) => c.normalize());
    if (parts.some((p) => p.isEmpty())) return IntersectCert.empty<T>();
    const reduced = this.reduceIntersect(parts);
    if (reduced.length === 1) return reduced[0];
    return IntersectCert.buildIntersectChain(reduced);
  }

  private flattenIntersect(): DomainCert<T>[] {
    const stack: DomainCert<T>[] = [];
    const push = (c: DomainCert<T>) => {
      if (c instanceof IntersectCert) {
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

  private static buildIntersectChain<T>(parts: DomainCert<T>[]): DomainCert<T> {
    return parts.slice(1).reduce((acc, cur) => new IntersectCert(acc, cur), parts[0]);
  }

  private reduceIntersect(parts: DomainCert<T>[]): DomainCert<T>[] {
    let acc: DomainCert<T>[] = [];
    for (const part of parts) {
      acc = this.pushIntersect(acc, part);
      if (acc.length === 1 && acc[0].isEmpty()) return acc;
    }
    return acc;
  }

  private pushIntersect(acc: DomainCert<T>[], next: DomainCert<T>): DomainCert<T>[] {
    if (acc.length === 0) return [next];
    const last = acc[acc.length - 1];
    if (last instanceof ContiguousCert && next instanceof ContiguousCert && last.witness === next.witness) {
      const merged = IntersectCert.intersectRanges(last, next);
      return merged ? [merged] : [IntersectCert.empty<T>()];
    }
    return [...acc, next];
  }

  private static intersectRanges<T>(a: ContiguousCert<T>, b: ContiguousCert<T>): ContiguousCert<T> | null {
    const witness = a.witness;
    const min = witness.compare(a.min, b.min) >= 0 ? a.min : b.min;
    const max = witness.compare(a.max, b.max) <= 0 ? a.max : b.max;
    if (witness.compare(min, max) > 0) return null;
    return new ContiguousCert(min, max, witness);
  }

  private static empty<T>(): DomainCert<T> {
    return new FiniteCert<T>([]);
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
}

