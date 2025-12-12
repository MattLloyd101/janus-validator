import { InterpolateStrategy } from './InterpolateStrategy';
import { IntegerInterpolateStrategy } from './IntegerInterpolateStrategy';
import { FloatInterpolateStrategy } from './FloatInterpolateStrategy';

/**
 * A contiguous type value with its interpolation strategy
 */
export interface ContiguousTypeValue {
  readonly name: string;
  readonly strategy: InterpolateStrategy;
}

/**
 * Contiguous types with their interpolation strategies
 */
export const ContiguousType = {
  INTEGER: {
    name: 'INTEGER',
    strategy: new IntegerInterpolateStrategy(),
  } as ContiguousTypeValue,
  FLOAT: {
    name: 'FLOAT',
    strategy: new FloatInterpolateStrategy(),
  } as ContiguousTypeValue,
} as const;

