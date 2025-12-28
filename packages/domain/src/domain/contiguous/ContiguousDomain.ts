import { AbstractDomain, type Domain } from "@/domain/AbstractDomain";
import { DomainCert } from "@/domain/cert/DomainCert";
import { ContiguousCert } from "@/domain/cert/ContiguousCert";
import { FiniteCert } from "@/domain/cert/FiniteCert";
import type { DiscreteOrdered } from "@/domain/witnesses/DiscreteOrdered";

export class ContiguousDomain<T> extends AbstractDomain<T> {
  readonly domainType = "contiguous-family";
  readonly witness: DiscreteOrdered<T>;

  private constructor(cert: DomainCert<T>, universe: ContiguousDomain<T> | undefined, witness: DiscreteOrdered<T>) {
    super(cert.withWitness(witness), universe);
    this.witness = witness;
  }

  static universe<T>(min: T, max: T, witness: DiscreteOrdered<T>): ContiguousDomain<T> {
    const uCert: DomainCert<T> = new ContiguousCert(min, max, witness);
    return new ContiguousDomain<T>(uCert, undefined, witness);
  }

  static range<T>(universe: ContiguousDomain<T>, min: T, max: T): ContiguousDomain<T> {
    const cert: DomainCert<T> = new ContiguousCert(min, max, universe.witness);
    return universe.fromCert(cert) as ContiguousDomain<T>;
  }

  static empty<T>(universe: ContiguousDomain<T>): ContiguousDomain<T> {
    return universe.fromCert(new FiniteCert<T>([])) as ContiguousDomain<T>;
  }

  protected fromCert(cert: DomainCert<T>): Domain<T> {
    const fixed = cert.withWitness(this.witness);
    return new ContiguousDomain<T>(fixed, this.universe as ContiguousDomain<T>, this.witness);
  }
}

