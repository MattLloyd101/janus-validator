import { Domain } from "../Domain";
import { RelationResult, DomainType } from "../types";
import { FiniteDomain } from "../domains/FiniteDomain";
import { ContiguousDomain } from "../domains/ContiguousDomain";
import { StringDomain } from "../domains/StringDomain";
import { RegexDomain } from "../domains/RegexDomain";
import { StructDomain } from "../domains/StructDomain";
import { QuantifierDomain } from "../domains/QuantifierDomain";
import { AlternationDomain } from "../domains/AlternationDomain";

export function encapsulates(sup: Domain<unknown>, sub: Domain<unknown>): RelationResult {
  if (sup.kind === DomainType.FINITE && sub.kind === DomainType.FINITE) {
    const missing = (sub as FiniteDomain<unknown>).all.filter((v) => !(sup as FiniteDomain<unknown>).contains(v));
    return missing.length === 0 ? { result: "true" } : { result: "false", reason: "finite missing elements" };
  }

  if (sup.kind === DomainType.CONTIGUOUS && sub.kind === DomainType.CONTIGUOUS) {
    const s = sup as ContiguousDomain<number | bigint>;
    const t = sub as ContiguousDomain<number | bigint>;
    return s.min <= t.min && s.max >= t.max ? { result: "true" } : { result: "false", reason: "range not covered" };
  }

  if (sup.kind === DomainType.STRING && sub.kind === DomainType.STRING) {
    const s = sup as StringDomain;
    const t = sub as StringDomain;
    return s.minLength <= t.minLength && s.maxLength >= t.maxLength
      ? { result: "true" }
      : { result: "false", reason: "string length not covered" };
  }

  if (sup.kind === DomainType.REGEX && sub.kind === DomainType.REGEX) {
    const s = sup as RegexDomain;
    const t = sub as RegexDomain;
    return s.pattern.source === t.pattern.source
      ? { result: "true" }
      : { result: "unknown", reason: "regex inclusion unsupported" };
  }

  if (sup.kind === DomainType.STRUCT && sub.kind === DomainType.STRUCT) {
    const s = sup as StructDomain<Record<string, unknown>>;
    const t = sub as StructDomain<Record<string, unknown>>;
    const sKeys = Object.keys(s.fields);
    const tKeys = Object.keys(t.fields);
    for (const key of tKeys) {
      if (!s.fields[key]) return { result: "false", reason: `missing field ${key}` };
      const rel = encapsulates(s.fields[key], t.fields[key]);
      if (rel.result !== "true") return rel;
    }
    if (s.strict === false && t.strict === true) return { result: "true" };
    if (s.strict === t.strict) return { result: "true" };
    if (s.strict === true && t.strict === false) {
      return { result: "false", reason: "superset disallows extra keys" };
    }
  }

  if (sup.kind === DomainType.QUANTIFIER && sub.kind === DomainType.QUANTIFIER) {
    const s = sup as QuantifierDomain<unknown>;
    const t = sub as QuantifierDomain<unknown>;
    if (s.min > t.min) return { result: "false", reason: "min length not covered" };
    if (s.max !== undefined && (t.max === undefined || s.max < t.max)) {
      return { result: "false", reason: "max length not covered" };
    }
    const rel = encapsulates(s.inner, t.inner);
    return rel.result === "true" ? { result: "true" } : rel;
  }

  if (sup.kind === DomainType.ALTERNATION) {
    const supOpts = (sup as AlternationDomain<unknown>).options;
    if (sub.kind === DomainType.ALTERNATION) {
      const subOpts = (sub as AlternationDomain<unknown>).options;
      const allCovered = subOpts.every((subOpt) =>
        supOpts.some((supOpt) => encapsulates(supOpt, subOpt).result === "true")
      );
      return allCovered ? { result: "true" } : { result: "false", reason: "alternation option not covered" };
    }
    const covered = supOpts.some((opt) => encapsulates(opt, sub).result === "true");
    return covered ? { result: "true" } : { result: "false", reason: "not covered by alternation" };
  }

  if (sup.kind === DomainType.CONTIGUOUS && sub.kind === DomainType.FINITE) {
    const s = sup as ContiguousDomain<number | bigint>;
    const allInside = (sub as FiniteDomain<unknown>).all.every((v) => s.contains(v));
    return allInside ? { result: "true" } : { result: "false", reason: "finite value outside range" };
  }

  return { result: "unknown", reason: "combination not supported" };
}

