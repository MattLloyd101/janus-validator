/**
 * @deprecated This module is deprecated. Import from '@janus-validator/lib' instead.
 * 
 * Example migration:
 * ```typescript
 * // Before
 * import { Email, UUID } from '@janus-validator/core/lib';
 * 
 * // After
 * import { Email, UUID } from '@janus-validator/lib';
 * ```
 * 
 * Or via the DSL:
 * ```typescript
 * import { Email, UUID } from '@janus-validator/dsl';
 * ```
 */

export * from './credentials';
export * from './contact';
export * from './network';
export * from './location';
export * from './finance';
export * from './datetime';
export * from './identifiers';
export * from './presets';
