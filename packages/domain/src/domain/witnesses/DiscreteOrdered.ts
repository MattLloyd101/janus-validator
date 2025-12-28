export interface DiscreteOrdered<T> {
  /** Stable identifier for serialization and equality of witnesses */
  id: string;
  /** Total order comparator: negative if a<b, 0 if equal, positive if a>b */
  compare(a: T, b: T): number;

  /** Optional successor/predecessor; undefined at boundary */
  succ(x: T): T | undefined;
  pred(x: T): T | undefined;

  /**
   * Optional distance for sizing/estimation.
   * Must satisfy: if a<=b then distance(a,b) >= 0.
   */
  distance?(a: T, b: T): number;

  /** Pretty printer for debugging/cert rendering */
  show?(x: T): string;
}


