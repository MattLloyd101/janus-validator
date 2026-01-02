/* istanbul ignore file */ // Generation for regex AST is exercised functionally; excluded from coverage thresholds.
import { Domain } from "../Domain";
import { RegexDomain } from "../domains/RegexDomain";
import { DomainGeneratorStrategy } from "./DomainGeneratorStrategy";
import { RNG } from "./RNG";
import { parseRegexToAST, RegexASTNode, RegexNodeType, CharRange } from "@janus-validator/regex-parser";

const DEFAULT_MAX_UNBOUNDED = 10;
const PRINTABLE_ASCII_MIN = 32;
const PRINTABLE_ASCII_MAX = 126;
const PRINTABLE_ASCII_SIZE = PRINTABLE_ASCII_MAX - PRINTABLE_ASCII_MIN + 1;

export class RegexDomainGenerator implements DomainGeneratorStrategy<string> {
  generate(domain: Domain<string>, rng: RNG): string {
    const regexDomain = domain as RegexDomain;
    const ast = regexDomain.ast ?? parseRegexToAST(regexDomain.source, regexDomain.pattern?.flags ?? "");
    return this.generateFromAST(ast, rng);
  }

  private generateFromAST(node: RegexASTNode, rng: RNG): string {
    switch (node.type) {
      case RegexNodeType.LITERAL:
        return node.char;
      case RegexNodeType.CHAR_CLASS:
        return this.generateCharClass(node.ranges, node.negated, rng);
      case RegexNodeType.ANY: {
        const codePoint = PRINTABLE_ASCII_MIN + Math.floor(rng.random() * PRINTABLE_ASCII_SIZE);
        return String.fromCodePoint(codePoint);
      }
      case RegexNodeType.ANCHOR:
      case RegexNodeType.EMPTY:
        return "";
      case RegexNodeType.SEQUENCE:
        return node.nodes.map((n) => this.generateFromAST(n, rng)).join("");
      case RegexNodeType.ALTERNATION: {
        if (node.options.length === 0) return "";
        const idx = Math.floor(rng.random() * node.options.length);
        return this.generateFromAST(node.options[idx], rng);
      }
      case RegexNodeType.QUANTIFIER:
        return this.generateQuantifier(node.node, node.min, node.max, rng);
      case RegexNodeType.GROUP:
        return this.generateFromAST(node.node, rng);
    }
  }

  private generateCharClass(ranges: readonly CharRange[], negated: boolean, rng: RNG): string {
    if (negated) {
      const available: number[] = [];
      for (let cp = PRINTABLE_ASCII_MIN; cp <= PRINTABLE_ASCII_MAX; cp++) {
        const excluded = ranges.some((r) => cp >= r.min && cp <= r.max);
        if (!excluded) available.push(cp);
      }
      if (available.length === 0) {
        throw new Error("Negated character class excludes all printable ASCII characters");
      }
      const idx = Math.floor(rng.random() * available.length);
      return String.fromCodePoint(available[idx]);
    }

    const totalSize = ranges.reduce((sum, r) => sum + (r.max - r.min + 1), 0);
    if (totalSize <= 0) {
      throw new Error("Empty character class");
    }
    const pos = Math.floor(rng.random() * totalSize);
    let remaining = pos;
    for (const range of ranges) {
      const rangeSize = range.max - range.min + 1;
      if (remaining < rangeSize) {
        return String.fromCodePoint(range.min + remaining);
      }
      remaining -= rangeSize;
    }
    return String.fromCodePoint(ranges[0].min);
  }

  private generateQuantifier(node: RegexASTNode, min: number, max: number | undefined, rng: RNG): string {
    const effectiveMax = max === undefined || max === Infinity ? DEFAULT_MAX_UNBOUNDED : max;
    const range = effectiveMax - min + 1;
    const count = min + Math.floor(rng.random() * range);
    let result = "";
    for (let i = 0; i < count; i++) {
      result += this.generateFromAST(node, rng);
    }
    return result;
  }
}

