import { RNG } from '../../RNG';
import { InterpolateStrategy } from './InterpolateStrategy';

/**
 * Interpolation strategy for integers
 * Generates uniformly distributed integers in [min, max] inclusive
 */
export class IntegerInterpolateStrategy implements InterpolateStrategy {
  interpolate(min: number, max: number, rng: RNG): number {
    const range = max - min;
    // floor(random * (range + 1)) + min ensures both min and max can be generated
    return Math.floor(rng.random() * (range + 1)) + min;
  }
}

