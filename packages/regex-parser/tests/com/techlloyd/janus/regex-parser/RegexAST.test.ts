import {
  RegexNodeType,
  isAny,
  isEmpty,
  isGroup,
  isQuantifier,
  isAnchor,
  isLiteral,
  isCharClass,
  LiteralNode,
  CharClassNode,
  AnyNode,
  AnchorNode,
  EmptyNode,
  GroupNode,
  QuantifierNode,
  AnchorKind,
} from "@/com/techlloyd/janus/regex-parser";

describe("RegexAST type guards", () => {
  const anchorNode: AnchorNode = { type: RegexNodeType.ANCHOR, kind: AnchorKind.START };
  const emptyNode: EmptyNode = { type: RegexNodeType.EMPTY };
  const groupNode: GroupNode = { type: RegexNodeType.GROUP, node: emptyNode, capturing: true };
  const anyNode: AnyNode = { type: RegexNodeType.ANY };
  const literalNode: LiteralNode = { type: RegexNodeType.LITERAL, char: "a" };
  const charClassNode: CharClassNode = { type: RegexNodeType.CHAR_CLASS, ranges: [], negated: false };
  const quantNode: QuantifierNode = { type: RegexNodeType.QUANTIFIER, node: literalNode, min: 0, max: 1 };

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
