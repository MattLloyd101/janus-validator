import { DiscreteOrdered } from "@/domain/witnesses/DiscreteOrdered";
import { DomainCert } from "./DomainCert";

export class ComplementCert<T> extends DomainCert<T> {
  readonly kind = "complement";
  readonly of: DomainCert<T>;
  readonly universe: DomainCert<T>;
  constructor(of: DomainCert<T>, universe: DomainCert<T>, id?: string) {
    super(id);
    this.of = of;
    this.universe = universe;
  }

  hash(): string {
    return `complement(${this.universe.hash()}|${this.of.hash()})`;
  }

  withWitness(witness: DiscreteOrdered<T>): DomainCert<T> {
    return new ComplementCert(this.of.withWitness(witness), this.universe.withWitness(witness), this.id);
  }

  contains(value: T): boolean {
    if (!this.universe.contains(value)) return false;
    return !this.of.contains(value);
  }

  isEmpty(): boolean {
    return false;
  }

  encapsulates(other: DomainCert<T>): boolean {
    if (this.equals(other)) return true;
    if (other.isEmpty()) return true;
    if (other instanceof ComplementCert) {
      // Only comparable when universes align.
      if (!this.universe.equals(other.universe)) return false;
      // U \ A ⊇ U \ B iff B ⊇ A (conservative)
      return other.of.encapsulates(this.of);
    }
    return false;
  }
}

