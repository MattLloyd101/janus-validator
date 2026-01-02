import { RNG } from "../RNG";
import { InterpolateStrategy } from "./InterpolateStrategy";

export class FloatInterpolateStrategy implements InterpolateStrategy {
  interpolate(min: number, max: number, rng: RNG): number {
    const range = max - min;
    return min + rng.random() * range;
  }
}

