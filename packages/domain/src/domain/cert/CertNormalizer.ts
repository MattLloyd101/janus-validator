import type { DomainCert } from "./DomainCert";
import { ComplementCert } from "./ComplementCert";
import { ContiguousCert } from "./ContiguousCert";
import { FiniteCert } from "./FiniteCert";
import { IntersectCert } from "./IntersectCert";
import { UnionCert } from "./UnionCert";

export class CertNormalizer {
  normalize<T>(cert: DomainCert<T>): DomainCert<T> {
    return this.normalizeCert(cert);
  }

  private normalizeCert<T>(cert: DomainCert<T>): DomainCert<T> {
    if (cert instanceof FiniteCert) return cert;
    if (cert instanceof ContiguousCert) return cert;
    if (cert instanceof ComplementCert) return this.normalizeComplement(cert);
    if (cert instanceof UnionCert) return this.normalizeUnion(cert);
    if (cert instanceof IntersectCert) return this.normalizeIntersect(cert);
    throw new Error("Unsupported certificate type for normalization");
  }

  private normalizeComplement<T>(cert: ComplementCert<T>): DomainCert<T> {
    const normalizedOf = this.normalizeCert(cert.of);
    const normalizedUniverse = this.normalizeCert(cert.universe);
    return new ComplementCert(normalizedOf, normalizedUniverse, cert.id);
  }

  private normalizeUnion<T>(cert: UnionCert<T>): DomainCert<T> {
    const flattened: DomainCert<T>[] = [];
    const push = (c: DomainCert<T>) => {
      const nc = this.normalizeCert(c);
      if (nc instanceof UnionCert) {
        push(nc.left);
        push(nc.right);
      } else if (!nc.isEmpty()) {
        flattened.push(nc);
      }
    };
    /* istanbul ignore next -- entry push invocation */
    push(cert.left);
    /* istanbul ignore next -- entry push invocation */
    push(cert.right);

    if (flattened.length === 0) return new FiniteCert<T>([]);

    // Merge contiguous segments and keep others as-is.
    const merged = ContiguousCert.mergeContiguous(flattened);

    // Dedupe by hash to enforce idempotence and determinism.
    const seen = new Map<string, DomainCert<T>>();
    for (const m of merged) {
      const h = m.hash();
      if (!seen.has(h)) seen.set(h, m);
    }
    const deduped = Array.from(seen.values());
    deduped.sort((a, b) => (a.hash() < b.hash() ? -1 : a.hash() > b.hash() ? 1 : 0));

    if (deduped.length === 1) return deduped[0];
    return deduped.slice(1).reduce((acc, cur) => new UnionCert(acc, cur), deduped[0]);
  }

  private normalizeIntersect<T>(cert: IntersectCert<T>): DomainCert<T> {
    const flattened: DomainCert<T>[] = [];
    const push = (c: DomainCert<T>) => {
      const nc = this.normalizeCert(c);
      if (nc instanceof IntersectCert) {
        push(nc.left);
        push(nc.right);
      } else {
        flattened.push(nc);
      }
    };
    /* istanbul ignore next -- entry push invocation */
    push(cert.left);
    /* istanbul ignore next -- entry push invocation */
    push(cert.right);

    if (flattened.some((c) => c.isEmpty())) return new FiniteCert<T>([]);

    const reduced = this.reduceIntersect(flattened);
    if (reduced.length === 0) return new FiniteCert<T>([]);
    if (reduced.length === 1) return reduced[0];

    // Dedupe by hash for determinism.
    const seen = new Map<string, DomainCert<T>>();
    for (const r of reduced) {
      const h = r.hash();
      if (!seen.has(h)) seen.set(h, r);
    }
    const deduped = Array.from(seen.values());
    deduped.sort((a, b) => (a.hash() < b.hash() ? -1 : a.hash() > b.hash() ? 1 : 0));

    if (deduped.length === 1) return deduped[0];
    return deduped.slice(1).reduce((acc, cur) => new IntersectCert(acc, cur), deduped[0]);
  }

  private reduceIntersect<T>(parts: DomainCert<T>[]): DomainCert<T>[] {
    let acc: DomainCert<T>[] = [];
    for (const part of parts) {
      acc = this.pushIntersect(acc, part);
      if (acc.length === 1 && acc[0].isEmpty()) return acc;
    }
    return acc;
  }

  private pushIntersect<T>(acc: DomainCert<T>[], next: DomainCert<T>): DomainCert<T>[] {
    if (acc.length === 0) return [next];
    const last = acc[acc.length - 1];
    if (last instanceof ContiguousCert && next instanceof ContiguousCert && last.witness === next.witness) {
      const merged = IntersectCert.intersectRanges(last, next);
      return merged ? [merged] : [new FiniteCert<T>([])];
    }
    return [...acc, next];
  }
}

export const certNormalizer = new CertNormalizer();

