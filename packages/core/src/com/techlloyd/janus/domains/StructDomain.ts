/**
 * Struct domain for object schemas with named fields.
 */

import { Domain } from './Domain';
import { DomainType, RelationResult, ok, no, unknown } from './types';
import { CustomGeneratorDomain } from './CustomGeneratorDomain';
import { FiniteDomain } from './FiniteDomain';
import { AlternationDomain } from './AlternationDomain';
import type { DomainsForObject } from '../Types';

/**
 * Checks if a domain accepts undefined as a valid value.
 * Used for struct field compatibility checking.
 */
function acceptsUndefined<T>(d: Domain<T>): boolean {
  // Unwrap CustomGeneratorDomain
  let dom: Domain<T> = d;
  while (dom instanceof CustomGeneratorDomain) {
    dom = dom.innerDomain;
  }

  if (dom instanceof FiniteDomain) {
    return dom.values.some((v) => v === undefined);
  }
  if (dom instanceof AlternationDomain) {
    return dom.alternatives.some((a) => acceptsUndefined(a));
  }
  return false;
}

/**
 * Domain representing an object/struct with named fields.
 * Parameterized by the output object type T.
 * 
 * @example
 * ```typescript
 * const domain = new StructDomain<{ name: string, age: number }>({
 *   name: stringDomain,
 *   age: numberDomain
 * }, true);
 * // schema type: { name: Domain<string>; age: Domain<number> }
 * ```
 */
export class StructDomain<T extends object = object> extends Domain<T> {
  readonly type = DomainType.STRUCT_DOMAIN;

  constructor(
    public readonly schema: DomainsForObject<T>,
    public readonly strict: boolean
  ) {
    super();
  }

  protected encapsulatesImpl(other: Domain<T>): RelationResult {
    if (!(other instanceof StructDomain)) {
      return no(`Domain type mismatch: ${other.type} not subset of ${this.type}`);
    }

    const aSchema = other.schema;
    const bSchema = this.schema;

    if (!aSchema || !bSchema) return unknown('Expected STRUCT_DOMAIN schema objects');

    if (other.strict === false && this.strict === true) {
      return no('Strictness tightened: non-strict is not subset of strict');
    }

    for (const key of Object.keys(aSchema) as (keyof T & string)[]) {
      const aField = aSchema[key];
      const bField = bSchema[key];
      if (!bField) return no(`Missing field in target schema: ${key}`);
      const res = bField.encapsulates(aField);
      if (res.result !== 'true') {
        return res.result === 'false' ? no(`${key}: ${res.reason}`) : unknown(`${key}: ${res.reason}`);
      }
    }

    for (const key of Object.keys(bSchema) as (keyof T & string)[]) {
      if (key in aSchema) continue;
      if (!acceptsUndefined(bSchema[key])) {
        return no(`New required field introduced: ${key}`);
      }
    }

    return ok();
  }
}
