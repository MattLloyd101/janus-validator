import { FiniteDomain } from '@/com/techlloyd/janus';
import { pbtConfig, pbtRng } from './utils/pbt';
import type { Lcg } from './utils/Lcg';

function mkUniverse(rng: Lcg): FiniteDomain<number> {
  const size = rng.int(0, 20);
  const vals: number[] = [];
  for (let i = 0; i < size; i++) vals.push(rng.int(-10, 10));
  return FiniteDomain.of(vals);
}

function mkSubsetOf(universe: FiniteDomain<number>, rng: Lcg): FiniteDomain<number> {
  // Create a derived domain so complement is relative to the universe.
  const pick: number[] = [];
  for (const v of universe.values) {
    if (rng.bool(0.5)) pick.push(v);
  }
  return universe.intersection(FiniteDomain.of(pick)) as FiniteDomain<number>;
}

describe('FiniteDomain properties (lightweight)', () => {
  it('set algebra laws hold (extensional equality)', () => {
    const { runs, seed } = pbtConfig();
    const rng = pbtRng(seed);
    const iterationOverrideRaw = process.env.JANUS_PBT_ITERATION;
    const iterationOverride =
      iterationOverrideRaw != null && iterationOverrideRaw.trim() !== ''
        ? Math.max(0, Math.floor(Number(iterationOverrideRaw)))
        : undefined;

    // Keep runtime predictable for larger runs.
    jest.setTimeout(Math.max(5_000, Math.ceil(runs / 25) * 1_000));

    const start = iterationOverride ?? 0;
    for (let i = start; i < runs; i++) {
      try {
        const U = mkUniverse(rng);
        const A = mkSubsetOf(U, rng);
        const B = mkSubsetOf(U, rng);
        const C = mkSubsetOf(U, rng);

        // Commutativity
        expect((A.union(B) as FiniteDomain<number>).equals(B.union(A) as FiniteDomain<number>)).toBe(true);
        expect((A.intersection(B) as FiniteDomain<number>).equals(B.intersection(A) as FiniteDomain<number>)).toBe(true);

        // Associativity
        expect(
          (A.union(B).union(C) as FiniteDomain<number>).equals(
            (A.union(B.union(C) as FiniteDomain<number>) as FiniteDomain<number>)
          )
        ).toBe(true);
        expect(
          (A.intersection(B).intersection(C) as FiniteDomain<number>).equals(
            (A.intersection(B.intersection(C) as FiniteDomain<number>) as FiniteDomain<number>)
          )
        ).toBe(true);

        // Idempotence
        expect((A.union(A) as FiniteDomain<number>).equals(A)).toBe(true);
        expect((A.intersection(A) as FiniteDomain<number>).equals(A)).toBe(true);

        // Absorption
        expect((A.union(A.intersection(B) as FiniteDomain<number>) as FiniteDomain<number>).equals(A)).toBe(true);
        expect((A.intersection(A.union(B) as FiniteDomain<number>) as FiniteDomain<number>).equals(A)).toBe(true);

        // Difference identities
        expect((A.difference(A) as FiniteDomain<number>).isEmpty()).toBe(true);
        expect((A.difference(FiniteDomain.of([])) as FiniteDomain<number>).equals(A)).toBe(true);
        expect((FiniteDomain.of([]).difference(A) as FiniteDomain<number>).isEmpty()).toBe(true);

        // Subset/superset consistency
        expect(A.isSubsetOf(B)).toBe(B.isSupersetOf(A));

        // Complement laws (relative to U for derived domains)
        const Ac = A.complement() as FiniteDomain<number>;
        expect((A.intersection(Ac) as FiniteDomain<number>).isEmpty()).toBe(true);
        expect((A.union(Ac) as FiniteDomain<number>).equals(U)).toBe(true);
        expect(A.isSubsetOf(U)).toBe(true);
        expect(U.isSupersetOf(A)).toBe(true);
      } catch (err) {
        const e = err as Error;
        throw new Error(
          `FiniteDomain PBT failed (seed=${seed}, runs=${runs}, iteration=${i}). ` +
            `Reproduce with: JANUS_PBT_SEED=${seed} JANUS_PBT_ITERATION=${i} npm -w @janus-validator/domain test\n` +
            (e?.stack ?? String(e))
        );
      }
    }
  });
});


