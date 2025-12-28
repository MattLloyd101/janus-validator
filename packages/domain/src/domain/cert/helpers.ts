import { DomainCert } from "./DomainCert";
import { ComplementCert } from "./ComplementCert";
import { ContiguousCert } from "./ContiguousCert";
import { FiniteCert } from "./FiniteCert";
import { IntersectCert } from "./IntersectCert";
import { UnionCert } from "./UnionCert";

export const isFiniteCert = <T>(cert: DomainCert<T>): cert is FiniteCert<T> =>
  cert instanceof FiniteCert;
export const isContiguousCert = <T>(cert: DomainCert<T>): cert is ContiguousCert<T> =>
  cert instanceof ContiguousCert;
export const isUnionCert = <T>(cert: DomainCert<T>): cert is UnionCert<T> =>
  cert instanceof UnionCert;
export const isIntersectCert = <T>(cert: DomainCert<T>): cert is IntersectCert<T> =>
  cert instanceof IntersectCert;
export const isComplementCert = <T>(cert: DomainCert<T>): cert is ComplementCert<T> =>
  cert instanceof ComplementCert;


