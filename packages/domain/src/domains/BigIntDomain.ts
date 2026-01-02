import { ContiguousDomain } from "./ContiguousDomain";

export class BigIntDomain extends ContiguousDomain<bigint> {
  constructor(min: bigint, max: bigint) {
    super(min, max);
  }
}

