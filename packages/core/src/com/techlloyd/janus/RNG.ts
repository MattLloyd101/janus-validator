/**
 * Random Number Generator interface
 * Returns a random number between 0 (inclusive) and 1 (exclusive)
 */
export interface RNG {
  /**
   * Returns a random number in the range [0, 1)
   */
  random(): number;
}

