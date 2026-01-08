/**
 * Discriminator enum for domain types.
 * 
 * Each domain has a `kind` property set to one of these values,
 * enabling type-safe pattern matching in generators and set operations.
 * 
 * @example
 * ```typescript
 * function handleDomain(domain: Domain<unknown>) {
 *   switch (domain.kind) {
 *     case DomainType.FINITE:
 *       return (domain as FiniteDomain<unknown>).all;
 *     case DomainType.CONTIGUOUS:
 *       return [(domain as ContiguousDomain<number>).min, (domain as ContiguousDomain<number>).max];
 *     // ... handle other domain types
 *   }
 * }
 * ```
 */
export enum DomainType {
  /** Domain with a finite set of discrete values (e.g., enums, booleans) */
  FINITE = "finite",
  /** Domain with a contiguous range of numeric values (integers or floats) */
  CONTIGUOUS = "contiguous",
  /** Domain for BigInt values with min/max bounds */
  BIGINT = "bigint",
  /** Domain for binary data (Uint8Array) with length constraints */
  BYTES = "bytes",
  /** Domain for Unicode strings with length constraints */
  STRING = "string",
  /** Domain for strings matching a regular expression pattern */
  REGEX = "regex",
  /** Domain for objects with a specific schema of field validators */
  STRUCT = "struct",
  /** Domain for arrays with a repeated element type and count constraints */
  QUANTIFIER = "quantifier",
  /** Domain representing a union of multiple possible types */
  ALTERNATION = "alternation",
  /** Domain for fixed-length tuples with typed elements */
  SEQUENCE = "sequence",
  /** Wrapper domain that provides custom value generation logic */
  CUSTOM_GENERATOR = "custom_generator",
  /** Wrapper domain that transforms values from an inner domain */
  TRANSFORM = "transform",
}

/**
 * Result of checking a relation between two domains.
 * 
 * Domain relations (like encapsulation) may not always be decidable,
 * so results can be:
 * - `true`: The relation definitely holds
 * - `false`: The relation definitely does not hold
 * - `unknown`: Cannot determine if the relation holds
 * 
 * @example
 * ```typescript
 * const result = encapsulates(domainA, domainB);
 * if (result.result === "true") {
 *   // domainA definitely encapsulates domainB
 * } else if (result.result === "false") {
 *   console.log("Reason:", result.reason);
 * } else {
 *   console.log("Cannot determine:", result.reason);
 * }
 * ```
 */
export type RelationResult =
  | { 
      /** The relation definitely holds */
      result: "true";
    }
  | { 
      /** The relation definitely does not hold */
      result: "false"; 
      /** Optional explanation of why the relation does not hold */
      reason?: string;
    }
  | { 
      /** Cannot determine if the relation holds */
      result: "unknown"; 
      /** Optional explanation of why the result is undecidable */
      reason?: string;
    };
