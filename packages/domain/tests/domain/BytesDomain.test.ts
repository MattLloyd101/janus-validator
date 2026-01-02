import { BytesDomain } from "@/domains/BytesDomain";

describe("BytesDomain", () => {
  it("enforces byte array length bounds", () => {
    const domain = new BytesDomain({ minLength: 1, maxLength: 2 });
    expect(domain.contains(new Uint8Array([]))).toBe(false);
    expect(domain.contains(new Uint8Array([1]))).toBe(true);
    expect(domain.contains(new Uint8Array([1, 2, 3]))).toBe(false);
  });

  it("throws on invalid bounds", () => {
    expect(() => new BytesDomain({ minLength: 3, maxLength: 2 })).toThrow("Invalid byte length bounds");
  });

  it("allows zero-length when minLength is zero", () => {
    const domain = new BytesDomain({ minLength: 0, maxLength: 1 });
    expect(domain.contains(new Uint8Array([]))).toBe(true);
    expect(domain.contains(new Uint8Array([1, 2]))).toBe(false);
  });

  it("contains rejects non-Uint8Array", () => {
    const domain = new BytesDomain({ minLength: 1, maxLength: 2 });
    expect(domain.contains([1, 2] as any)).toBe(false);
  });
});
