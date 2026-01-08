import {
  parseRegexToAST,
  RegexNodeType,
  isAlternation,
  isSequence,
  isQuantifier,
  isCharClass,
  isAnchor,
  isLiteral,
  SequenceNode,
  AlternationNode,
  CharClassNode,
  GroupNode,
  QuantifierNode,
  LiteralNode,
} from "@/index";

describe("parseRegexToAST portable subset", () => {
  it("returns empty node for empty pattern", () => {
    const ast = parseRegexToAST("");
    expect(ast.type === RegexNodeType.EMPTY || (isSequence(ast) && ast.nodes.length === 0)).toBe(true);
  });

  it("parses literals, anchors, and quantifiers", () => {
    const ast = parseRegexToAST("^ab+$");
    expect(ast.type).toBe(RegexNodeType.SEQUENCE);
    if (isSequence(ast)) {
      expect(ast.nodes[0].type).toBe(RegexNodeType.ANCHOR);
      expect(ast.nodes[1].type).toBe(RegexNodeType.LITERAL);
      expect(ast.nodes[2].type).toBe(RegexNodeType.QUANTIFIER);
      expect(ast.nodes[3].type).toBe(RegexNodeType.ANCHOR);
    }
  });

  it("parses alternation", () => {
    const ast = parseRegexToAST("a|b");
    expect(isAlternation(ast)).toBe(true);
    if (isAlternation(ast)) {
      expect(ast.options).toHaveLength(2);
    }
  });

  it("parses groups and non-capturing", () => {
    const ast = parseRegexToAST("(a)(?:b)");
    expect(isSequence(ast)).toBe(true);
    if (isSequence(ast)) {
      expect(ast.nodes[0].type).toBe(RegexNodeType.GROUP);
      expect(ast.nodes[1].type).toBe(RegexNodeType.GROUP);
      const nonCapturing = ast.nodes[1] as GroupNode;
      expect(nonCapturing.capturing).toBe(false);
    }
  });

  it("parses char classes and ranges", () => {
    const ast = parseRegexToAST("[a-c]");
    expect(isCharClass(ast)).toBe(true);
    if (isCharClass(ast)) {
      expect(ast.ranges[0]).toEqual({ min: "a".codePointAt(0), max: "c".codePointAt(0) });
    }
  });

  it("merges adjacent ranges", () => {
    const ast = parseRegexToAST("[a-bc-d]");
    if (isCharClass(ast)) {
      expect(ast.ranges.length).toBe(1);
      expect(ast.ranges[0].min).toBe("a".codePointAt(0));
      expect(ast.ranges[0].max).toBe("d".codePointAt(0));
    }
  });

  it("parses quantifier bounds", () => {
    const ast = parseRegexToAST("a{2,4}");
    const quant = isQuantifier(ast) ? ast : (isSequence(ast) ? ast.nodes.find(isQuantifier) : undefined);
    expect(quant?.min).toBe(2);
    expect(quant?.max).toBe(4);
  });

  it("parses open range quantifier to infinity", () => {
    const ast = parseRegexToAST("a{2,}");
    const quant = isQuantifier(ast) ? ast : (isSequence(ast) ? ast.nodes.find(isQuantifier) : undefined);
    expect(quant?.min).toBe(2);
    expect(quant?.max).toBe(Infinity);
  });

  it("parses escapes for common controls", () => {
    const ast = parseRegexToAST("\\n\\r\\t\\f\\v\\0");
    expect(isSequence(ast)).toBe(true);
  });

  it("parses star and question quantifiers", () => {
    const ast = parseRegexToAST("a*b?");
    expect(isSequence(ast)).toBe(true);
    if (isSequence(ast)) {
      const quantNodes = ast.nodes.filter(isQuantifier);
      expect(quantNodes).toHaveLength(2);
    }
  });

  it("parses start and end anchors", () => {
    const ast = parseRegexToAST("^$");
    expect(isSequence(ast)).toBe(true);
    if (isSequence(ast)) {
      expect(ast.nodes[0].type).toBe(RegexNodeType.ANCHOR);
      expect(ast.nodes[1].type).toBe(RegexNodeType.ANCHOR);
    }
  });

  it("parses negated character class", () => {
    const ast = parseRegexToAST("[^a]");
    expect(isCharClass(ast)).toBe(true);
    if (isCharClass(ast)) {
      expect(ast.negated).toBe(true);
    }
  });

  it("parses dot as any node", () => {
    const ast = parseRegexToAST(".");
    expect(ast.type).toBe(RegexNodeType.ANY);
  });

  it("normalizes disjoint char class ranges", () => {
    const ast = parseRegexToAST("[a-cx-z]");
    if (isCharClass(ast)) {
      expect(ast.ranges.length).toBe(2);
    }
  });

  it("parses non-capturing group flag", () => {
    const ast = parseRegexToAST("(?:a)");
    expect(isSequence(ast)).toBe(false);
    expect(ast.type).toBe(RegexNodeType.GROUP);
    const group = ast as GroupNode;
    expect(group.capturing).toBe(false);
  });

  it("parses multiple alternations", () => {
    const ast = parseRegexToAST("a|b|c");
    expect(isAlternation(ast)).toBe(true);
    if (isAlternation(ast)) {
      expect(ast.options.length).toBe(3);
    }
  });

  it("type guards cover literal and group", () => {
    const ast = parseRegexToAST("(a)");
    expect(ast.type).toBe(RegexNodeType.GROUP);
  });

  it("exercises all type guards", () => {
    const ast = parseRegexToAST("^a|b$");
    expect(isAlternation(ast)).toBe(true);
    if (isAlternation(ast)) {
      expect(isSequence(ast.options[0])).toBe(true);
      const seq0 = ast.options[0] as SequenceNode;
      expect(seq0.nodes.some(isAnchor)).toBe(true);
      expect(isAnchor(seq0.nodes[0])).toBe(true);
      expect(isLiteral(seq0.nodes[1])).toBe(true);
      const seq1 = ast.options[1] as SequenceNode;
      expect(isAnchor(seq1.nodes[1])).toBe(true);
      expect(isLiteral(seq1.nodes[0])).toBe(true);
    }
  });

  it("parses escaped backslash as literal", () => {
    const ast = parseRegexToAST("\\\\");
    const lit = isLiteral(ast) ? ast : (isSequence(ast) ? ast.nodes[0] as LiteralNode : undefined);
    expect(lit?.char).toBe("\\");
  });

  it("parses escaped char class member", () => {
    const ast = parseRegexToAST("[\\n]");
    if (isCharClass(ast)) {
      expect(ast.ranges[0].min).toBe("\n".codePointAt(0));
    }
  });
});

describe("parseRegexToAST rejections (portable subset)", () => {
  it("rejects flags", () => {
    expect(() => parseRegexToAST("abc", "i")).toThrow("Unsupported regex flags");
  });

  it("rejects lookarounds", () => {
    expect(() => parseRegexToAST("(?=a)")).toThrow(/Unsupported regex construct/);
    expect(() => parseRegexToAST("(?!a)")).toThrow(/Unsupported regex construct/);
  });

  it("rejects backreferences", () => {
    expect(() => parseRegexToAST("(a)\\1")).toThrow(/Unsupported regex construct/);
  });

  it("rejects non-portable escapes", () => {
    expect(() => parseRegexToAST("\\d")).toThrow(/not portable/);
    expect(() => parseRegexToAST("\\w+")).toThrow(/not portable/);
    expect(() => parseRegexToAST("\\s")).toThrow(/not portable/);
  });

  it("rejects inline flag groups", () => {
    expect(() => parseRegexToAST("(?i:abc)")).toThrow(/Unsupported regex construct/);
  });

  it("rejects missing repetition close", () => {
    expect(() => parseRegexToAST("a{2")).toThrow(/Expected '}'/);
  });

  it("rejects empty repetition body", () => {
    expect(() => parseRegexToAST("a{}")).toThrow(/Expected number/);
  });

  it("rejects unterminated group", () => {
    expect(() => parseRegexToAST("(")).toThrow("Expected ')'");
  });

  it("rejects trailing escape", () => {
    expect(() => parseRegexToAST("a\\")).toThrow(/Unexpected end of pattern after escape/);
  });

  it("rejects unterminated char class", () => {
    expect(() => parseRegexToAST("[abc")).toThrow("Expected ']'");
  });
});
