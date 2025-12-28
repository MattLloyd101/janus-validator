import type { DiscreteOrdered } from "@/domain/witnesses/DiscreteOrdered";
import type { SerializedDomainCert } from "./Serialize";

export type DomainKind = "finite" | "contiguous" | "complement" | "union" | "intersect";

export abstract class DomainCert<T> {
  abstract readonly kind: DomainKind;
  readonly id?: string;
  protected constructor(id?: string) {
    this.id = id;
  }

  abstract hash(): string;
  abstract withWitness(witness: DiscreteOrdered<T>): DomainCert<T>;
  abstract contains(value: T): boolean;
  abstract isEmpty(): boolean;
  abstract encapsulates(other: DomainCert<T>): boolean;
  abstract serialize(): SerializedDomainCert<T>;

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

}
