import { Domain } from "../Domain";
import { RNG } from "./RNG";

export interface DomainGeneratorStrategy<T> {
  generate(domain: Domain<T>, rng: RNG): T;
}

