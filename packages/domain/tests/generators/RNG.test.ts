import { defaultRng } from "@/generators";

describe("RNG", () => {
  it("produces numbers in [0,1)", () => {
    const v = defaultRng.random();
    expect(v).toBeGreaterThanOrEqual(0);
    expect(v).toBeLessThan(1);
  });
});

