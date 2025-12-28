import type { DiscreteOrdered } from "../src";

export const integerWitness: DiscreteOrdered<number> = {
  compare: (a, b) => a - b,
  succ: (x) => x + 1,
  pred: (x) => x - 1,
  distance: (a, b) => b - a,
  show: (x) => x.toString()
};

