import { DomainCert } from "./cert/DomainCert";
import { certNormalizer } from "./cert/CertNormalizer";
import { ComplementCert } from "./cert/ComplementCert";
import { IntersectCert } from "./cert/IntersectCert";
import { UnionCert } from "./cert/UnionCert";

export interface Domain<T> {
  readonly domainType: string;
  readonly universe: Domain<T>;
  readonly cert: DomainCert<T>;

  isEmpty(): boolean;
  isDefinedAt(value: T): boolean;

  union(other: Domain<T>): Domain<T>;
  intersect(other: Domain<T>): Domain<T>;
  complement(): Domain<T>;

  encapsulates(other: Domain<T>): boolean;
  equals(other: Domain<T>): boolean;
}

export abstract class AbstractDomain<T> implements Domain<T> {
  abstract readonly domainType: string;

  readonly cert: DomainCert<T>;
  readonly universe: Domain<T>;

  protected constructor(cert: DomainCert<T>, universe?: Domain<T>) {
    this.cert = certNormalizer.normalize(cert);
    this.universe = (universe ?? (this as unknown as Domain<T>));
  }

  isEmpty(): boolean {
    return this.cert.isEmpty();
  }

  isDefinedAt(value: T): boolean {
    return this.cert.contains(value);
  }

  union(other: Domain<T>): Domain<T> {
    this.assertSameUniverse(other);
    return this.fromCert(new UnionCert(this.cert, other.cert));
  }

  intersect(other: Domain<T>): Domain<T> {
    this.assertSameUniverse(other);
    return this.fromCert(new IntersectCert(this.cert, other.cert));
  }

  complement(): Domain<T> {
    return this.fromCert(new ComplementCert(this.cert, this.universe.cert));
  }

  equals(other: Domain<T>): boolean {
    this.assertSameUniverse(other);
    return this.cert.hash() === other.cert.hash();
  }

  encapsulates(other: Domain<T>): boolean {
    this.assertSameUniverse(other);
    return this.cert.encapsulates(other.cert);
  }

  protected abstract fromCert(cert: DomainCert<T>): Domain<T>;

  protected assertSameUniverse(other: Domain<T>) {
    if (this.universe !== other.universe) {
      throw new Error("Universe mismatch");
    }
  }
}
