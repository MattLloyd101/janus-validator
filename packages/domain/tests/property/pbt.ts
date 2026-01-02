import fc from "fast-check";

type Profile = "ci" | "complete";

const rawProfile = (process.env.JANUS_PBT_PROFILE || "ci").toLowerCase();
const profile: Profile = rawProfile === "complete" || rawProfile === "long" ? "complete" : "ci";

const parsedSeed = process.env.JANUS_PBT_SEED ? Number(process.env.JANUS_PBT_SEED) : undefined;
const seed = Number.isFinite(parsedSeed) ? parsedSeed : Date.now();

const parsedRuns = process.env.JANUS_PBT_NUM_RUNS ? Number(process.env.JANUS_PBT_NUM_RUNS) : undefined;
const numRuns = Number.isFinite(parsedRuns) ? parsedRuns : profile === "complete" ? 300 : 75;

export const pbtConfig = { profile, seed, numRuns };

export function pbt(property: fc.IProperty<unknown>): void {
  fc.assert(property, { seed, numRuns });
}

export { fc };

