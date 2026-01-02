import {
  RegexNodeType,
  isAny,
  isEmpty,
  isGroup,
  isQuantifier,
  isAnchor,
  isLiteral,
  isCharClass,
} from "@/com/techlloyd/janus/regex-parser";

describe("RegexAST type guards", () => {
  const anchorNode = { type: RegexNodeType.ANCHOR, kind: "start" } as any;
  const emptyNode = { type: RegexNodeType.EMPTY } as any;
  const groupNode = { type: RegexNodeType.GROUP, node: emptyNode, capturing: true } as any;
  const anyNode = { type: RegexNodeType.ANY } as any;
  const literalNode = { type: RegexNodeType.LITERAL, char: "a" } as any;
  const charClassNode = { type: RegexNodeType.CHAR_CLASS, ranges: [], negated: false } as any;
  const quantNode = { type: RegexNodeType.QUANTIFIER, node: literalNode, min: 0, max: 1 } as any;

  it("identifies anchors and empty", () => {
    expect(isAnchor(anchorNode)).toBe(true);
    expect(isEmpty(emptyNode)).toBe(true);
  });

  it("identifies group and any", () => {
    expect(isGroup(groupNode)).toBe(true);
    expect(isAny(anyNode)).toBe(true);
  });

  it("identifies literal, char class, quantifier", () => {
    expect(isLiteral(literalNode)).toBe(true);
    expect(isCharClass(charClassNode)).toBe(true);
    expect(isQuantifier(quantNode)).toBe(true);
  });
});

