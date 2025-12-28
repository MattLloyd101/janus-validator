import type { DiscreteOrdered } from "@/domain/witnesses/DiscreteOrdered";

export type DomainKind = "finite" | "contiguous" | "complement" | "union" | "intersect";

export abstract class DomainCert<T> {
  abstract readonly kind: DomainKind;
  readonly id?: string;
  protected constructor(id?: string) {
    this.id = id;
  }

  abstract hash(): string;
  abstract withWitness(witness: DiscreteOrdered<T>): DomainCert<T>;
  abstract normalize(): DomainCert<T>;
  abstract contains(value: T): boolean;
  abstract isEmpty(): boolean;
  abstract encapsulates(other: DomainCert<T>): boolean;

  equals(other: DomainCert<T>): boolean {
    return this.hash() === other.hash();
  }

  protected renderValue(v: unknown): string {
    if (typeof v === "number" || typeof v === "string" || typeof v === "boolean" || v === null || v === undefined) {
      return String(v);
    }
    try {
      return JSON.stringify(v);
    } catch {
      return String(v);
    }
  }

  protected renderValues(values: readonly unknown[]): string {
    return values.map((v) => this.renderValue(v)).join(",");
  }

  private static witnessIds = new WeakMap<object, number>();
  private static witnessIdSeq = 0;
  protected getWitnessId(obj: object): number {
    const existing = DomainCert.witnessIds.get(obj);
    if (existing !== undefined) return existing;
    DomainCert.witnessIdSeq += 1;
    DomainCert.witnessIds.set(obj, DomainCert.witnessIdSeq);
    return DomainCert.witnessIdSeq;
  }
}

export type CertProblem =
  | { code: "INVALID_BOUND_ORDER"; message: string }
  | { code: "MISSING_WITNESS"; message: string }
  | { code: "NON_CANONICAL"; message: string }
  | { code: "UNSUPPORTED"; message: string }
  | { code: "INVALID_FINITE_VALUES"; message: string };

export type CertCheckResult =
  | { ok: true; problems?: CertProblem[] }
  | { ok: false; problems: CertProblem[] };

