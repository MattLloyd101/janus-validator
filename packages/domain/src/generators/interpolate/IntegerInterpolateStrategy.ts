import { RNG } from "../RNG";
import { InterpolateStrategy } from "./InterpolateStrategy";

export class IntegerInterpolateStrategy implements InterpolateStrategy {
  interpolate(min: number, max: number, rng: RNG): number {
    const range = max - min;
    return Math.floor(rng.random() * (range + 1)) + min;
  }
}

