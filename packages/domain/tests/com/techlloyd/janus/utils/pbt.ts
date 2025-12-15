import { Lcg } from './Lcg';

function envNumber(name: string, fallback: number): number {
  const raw = process.env[name];
  if (raw == null || raw.trim() === '') return fallback;
  const n = Number(raw);
  return Number.isFinite(n) ? n : fallback;
}

function envInt(name: string, fallback: number): number {
  return Math.floor(envNumber(name, fallback));
}

function clamp(n: number, min: number, max: number): number {
  return Math.max(min, Math.min(max, n));
}

function envSeed32(name: string): number | undefined {
  const raw = process.env[name];
  if (raw == null || raw.trim() === '') return undefined;
  const n = Number(raw);
  if (!Number.isFinite(n)) return undefined;
  return Math.floor(n) >>> 0;
}

function randomSeed32(): number {
  // Prefer Math.random() so local runs are easy; keep it within uint32.
  return (Math.floor(Math.random() * 0x1_0000_0000) >>> 0);
}

export function pbtConfig(): { runs: number; seed: number } {
  const profile = (process.env.JANUS_PBT_PROFILE ?? '').toLowerCase().trim();

  // Defaults: fast locally; allow CI (or scripts) to opt into "long".
  const defaultRuns = profile === 'long' ? 25_000 : 250;

  const runs0 = clamp(envInt('JANUS_PBT_RUNS', defaultRuns), 1, 1_000_000);
  const seed = envSeed32('JANUS_PBT_SEED') ?? randomSeed32();

  const iterationOverride = envInt('JANUS_PBT_ITERATION', -1);
  if (Number.isFinite(iterationOverride) && iterationOverride >= 0) {
    // If the user asks for a specific iteration, run exactly that iteration:
    // start = iteration, runs = iteration + 1.
    const it = clamp(iterationOverride, 0, 1_000_000);
    return { runs: it + 1, seed };
  }

  return { runs: runs0, seed };
}

export function pbtRng(seed: number): Lcg {
  return new Lcg(seed);
}


