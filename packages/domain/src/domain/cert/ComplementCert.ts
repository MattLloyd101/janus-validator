import { DiscreteOrdered } from "@/domain/witnesses/DiscreteOrdered";
import { DomainCert } from "./DomainCert";

export class ComplementCert<T> extends DomainCert<T> {
  readonly kind = "complement";
  readonly of: DomainCert<T>;
  constructor(of: DomainCert<T>, id?: string) {
    super(id);
    this.of = of;
  }

  hash(): string {
    return `complement(${this.of.hash()})`;
  }

  withWitness(witness: DiscreteOrdered<T>): DomainCert<T> {
    return new ComplementCert(this.of.withWitness(witness), this.id);
  }

  normalize(): DomainCert<T> {
    return new ComplementCert(this.of.normalize(), this.id);
  }

  contains(value: T): boolean {
    return !this.of.contains(value);
  }

  isEmpty(): boolean {
    return false;
  }

  encapsulates(other: DomainCert<T>): boolean {
    if (this.equals(other)) return true;
    if (other.isEmpty()) return true;
    return false;
  }
}

