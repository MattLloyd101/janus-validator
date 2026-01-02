/**
 * Random Number Generator interface
 * Returns a random number between 0 (inclusive) and 1 (exclusive)
 */
export interface RNG {
  random(): number;
}

export const defaultRng: RNG = {
  random: () => Math.random(),
};

