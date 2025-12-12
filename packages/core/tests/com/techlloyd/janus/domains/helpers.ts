import type { RNG } from '@/com/techlloyd/janus/RNG';

/**
 * Deterministic RNG from a fixed sequence of [0,1) values.
 * If the sequence runs out, the last value is repeated.
 */
export function rngFromSequence(values: number[]): RNG {
  if (values.length === 0) {
    throw new Error('rngFromSequence requires at least one value');
  }
  let i = 0;
  return {
    random: () => {
      const idx = Math.min(i, values.length - 1);
      const v = values[idx];
      i++;
      return v;
    },
  };
}


