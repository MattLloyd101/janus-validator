/**
 * @janus-validator/dsl - Concise DSL for Janus Validator
 * 
 * This package re-exports the DSL from @janus-validator/core for convenience.
 * You can use either:
 *   - import { B, S, I } from '@janus-validator/dsl'
 *   - import { B, S, I } from '@janus-validator/core/DSL'
 * 
 * @example
 * ```typescript
 * import { B, S, I, N, L, R, O, Bytes, Or, Seq, optional, oneOrMore } from '@janus-validator/dsl';
 * 
 * const user = O({
 *   name: S(1, 50),
 *   age: I(0, 150),
 *   active: B(),
 * });
 * ```
 */

export * from '@janus-validator/core/DSL';
