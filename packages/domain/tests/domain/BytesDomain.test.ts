import { BytesDomain } from "@/domains/BytesDomain";

describe("BytesDomain", () => {
  it("validates Uint8Array of correct length", () => {
    const domain = new BytesDomain({ minLength: 2, maxLength: 4 });
    expect(domain.contains(new Uint8Array([1, 2]))).toBe(true);
    expect(domain.contains(new Uint8Array([1, 2, 3, 4]))).toBe(true);
    expect(domain.contains(new Uint8Array([1]))).toBe(false);
    expect(domain.contains(new Uint8Array([1, 2, 3, 4, 5]))).toBe(false);
  });

  it("rejects non-Uint8Array values", () => {
    const domain = new BytesDomain({ minLength: 1, maxLength: 10 });
    // Testing defensive behavior - arrays should not be accepted
    expect(domain.contains([1, 2])).toBe(false);
  });

  it("throws on invalid bounds", () => {
    // minLength negative
    expect(() => new BytesDomain({ minLength: -1, maxLength: 10 })).toThrow("Invalid byte length bounds");
    // maxLength < minLength
    expect(() => new BytesDomain({ minLength: 10, maxLength: 5 })).toThrow("Invalid byte length bounds");
  });
});
