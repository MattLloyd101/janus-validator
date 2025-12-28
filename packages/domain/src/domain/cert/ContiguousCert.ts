import { DomainCert } from "./DomainCert";
import type { DiscreteOrdered } from "@/domain/witnesses/DiscreteOrdered";
import type { DomainCert as AnyDomainCert } from "./DomainCert";
import { FiniteCert } from "./FiniteCert";

export class ContiguousCert<T> extends DomainCert<T> {
  readonly kind = "contiguous";
  readonly min: T;
  readonly max: T;
  readonly witness: DiscreteOrdered<T>;
  constructor(min: T, max: T, witness: DiscreteOrdered<T>, id?: string) {
    super(id);
    this.min = min;
    this.max = max;
    this.witness = witness;
  }

  hash(): string {
    return `contiguous:${this.renderValue(this.min)}:${this.renderValue(this.max)}:${this.getWitnessId(
      this.witness as object
    )}`;
  }

  withWitness(witness: DiscreteOrdered<T>): DomainCert<T> {
    return new ContiguousCert(this.min, this.max, witness, this.id);
  }

  contains(value: T): boolean {
    const cmpMin = this.witness.compare(this.min, value);
    const cmpMax = this.witness.compare(value, this.max);
    return cmpMin <= 0 && cmpMax <= 0;
  }

  isEmpty(): boolean {
    return false;
  }

  encapsulates(other: DomainCert<T>): boolean {
    if (other.isEmpty()) return true;
    if (other instanceof ContiguousCert && other.witness === this.witness) {
      return this.witness.compare(this.min, other.min) <= 0 && this.witness.compare(other.max, this.max) <= 0;
    }
    if (other instanceof FiniteCert) {
      return other.values.every((v) => this.contains(v));
    }
    return false;
  }

  static mergeContiguous<T>(parts: AnyDomainCert<T>[]): AnyDomainCert<T>[] {
    // Separate contiguous certs from everything else.
    const contiguous = parts.filter((p): p is ContiguousCert<T> => p instanceof ContiguousCert);
    const others = parts.filter((p) => !(p instanceof ContiguousCert));

    // Group contiguous ranges by witness identity (only merge within same witness).
    const grouped = new Map<unknown, ContiguousCert<T>[]>();
    for (const c of contiguous) {
      const key = c.witness;
      const list = grouped.get(key) ?? [];
      list.push(c);
      grouped.set(key, list);
    }

    const merged: AnyDomainCert<T>[] = [];
    for (const [_w, list] of grouped.entries()) {
      // Sort by min bound to enable linear merging.
      list.sort((a, b) => a.witness.compare(a.min, b.min));
      const compacted: ContiguousCert<T>[] = [];
      for (const item of list) {
        const last = compacted[compacted.length - 1];
        if (!last) {
          compacted.push(item);
          continue;
        }
        // Merge if overlapping or adjacent; otherwise start a new segment.
        if (ContiguousCert.rangesOverlapOrAdjacent(last, item)) {
          compacted[compacted.length - 1] = ContiguousCert.mergeRanges(last, item);
        } else {
          compacted.push(item);
        }
      }
      merged.push(...compacted);
    }

    // Preserve non-contiguous certs alongside merged contiguous results.
    return merged.concat(others);
  }

  private static rangesOverlapOrAdjacent<T>(a: ContiguousCert<T>, b: ContiguousCert<T>): boolean {
    const cmp = a.witness.compare(a.max, b.min);
    if (cmp > 0) return true;
    if (cmp === 0) return true;
    const next = a.witness.succ(a.max);
    return next !== undefined && a.witness.compare(next, b.min) === 0;
  }

  private static mergeRanges<T>(a: ContiguousCert<T>, b: ContiguousCert<T>): ContiguousCert<T> {
    const witness = a.witness;
    const min = witness.compare(a.min, b.min) <= 0 ? a.min : b.min;
    const max = witness.compare(a.max, b.max) >= 0 ? a.max : b.max;
    return new ContiguousCert(min, max, witness);
  }
}

