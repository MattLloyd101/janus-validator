import { ContiguousCert, DomainCert, FiniteCert } from "@/index";
import { integerWitness } from "../../helpers";

describe("DomainCert base behaviors", () => {
  test("renderValue catches stringify failures", () => {
    const obj: any = {};
    obj.self = obj; // circular to trigger JSON.stringify failure
    const cert = new FiniteCert([obj]);
    // hash should not throw due to catch in renderValue
    expect(() => cert.hash()).not.toThrow();
  });

  test("witness id is stable across repeated hashes", () => {
    const cert = new ContiguousCert(0, 1, integerWitness);
    const first = cert.hash();
    const second = cert.hash();
    expect(first).toBe(second);
  });
});

