import { RNG } from "../RNG";

export interface InterpolateStrategy {
  interpolate(min: number, max: number, rng: RNG): number;
}

