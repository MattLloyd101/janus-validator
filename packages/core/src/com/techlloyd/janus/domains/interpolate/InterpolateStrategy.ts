import { RNG } from '../../RNG';

/**
 * Strategy interface for interpolating values within a range
 */
export interface InterpolateStrategy {
  interpolate(min: number, max: number, rng: RNG): number;
}

