export type SerializedWitness = { id: string };
export type SerializedFiniteCert<T> = { kind: "finite"; id?: string; values: readonly T[] };
export type SerializedContiguousCert<T> = {
  kind: "contiguous";
  id?: string;
  min: T;
  max: T;
  witness: SerializedWitness;
};
export type SerializedUnionCert<T> = { kind: "union"; id?: string; left: SerializedDomainCert<T>; right: SerializedDomainCert<T> };
export type SerializedIntersectCert<T> = { kind: "intersect"; id?: string; left: SerializedDomainCert<T>; right: SerializedDomainCert<T> };
export type SerializedComplementCert<T> = { kind: "complement"; id?: string; of: SerializedDomainCert<T>; universe: SerializedDomainCert<T> };

export type SerializedDomainCert<T> =
  | SerializedFiniteCert<T>
  | SerializedContiguousCert<T>
  | SerializedUnionCert<T>
  | SerializedIntersectCert<T>
  | SerializedComplementCert<T>;

