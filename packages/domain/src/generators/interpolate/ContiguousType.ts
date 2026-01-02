import { InterpolateStrategy } from "./InterpolateStrategy";
import { IntegerInterpolateStrategy } from "./IntegerInterpolateStrategy";
import { FloatInterpolateStrategy } from "./FloatInterpolateStrategy";

export interface ContiguousTypeValue {
  readonly name: string;
  readonly strategy: InterpolateStrategy;
}

export const ContiguousType = {
  INTEGER: {
    name: "INTEGER",
    strategy: new IntegerInterpolateStrategy(),
  } as ContiguousTypeValue,
  FLOAT: {
    name: "FLOAT",
    strategy: new FloatInterpolateStrategy(),
  } as ContiguousTypeValue,
} as const;

