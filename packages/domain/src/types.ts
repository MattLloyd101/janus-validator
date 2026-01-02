export enum DomainType {
  FINITE = "finite",
  CONTIGUOUS = "contiguous",
  BIGINT = "bigint",
  BYTES = "bytes",
  STRING = "string",
  REGEX = "regex",
  STRUCT = "struct",
  QUANTIFIER = "quantifier",
  ALTERNATION = "alternation",
}

export type RelationResult =
  | { result: "true" }
  | { result: "false"; reason: string }
  | { result: "unknown"; reason: string };

