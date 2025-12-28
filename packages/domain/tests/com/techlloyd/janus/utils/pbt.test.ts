import { pbtConfig } from './pbt';

describe('pbt utils', () => {
  const prev = { ...process.env };

  afterEach(() => {
    process.env = { ...prev };
  });

  it('defaults to short profile (250 runs) and random seed when unset', () => {
    delete process.env.JANUS_PBT_PROFILE;
    delete process.env.JANUS_PBT_RUNS;
    delete process.env.JANUS_PBT_SEED;
    delete process.env.JANUS_PBT_ITERATION;
    const cfg = pbtConfig();
    expect(cfg.runs).toBe(250);
    expect(Number.isInteger(cfg.seed)).toBe(true);
  });

  it('supports long profile defaults and overrides via env vars', () => {
    process.env.JANUS_PBT_PROFILE = 'long';
    const cfg0 = pbtConfig();
    expect(cfg0.runs).toBe(25_000);

    process.env.JANUS_PBT_RUNS = '500';
    process.env.JANUS_PBT_SEED = '123';
    const cfg1 = pbtConfig();
    expect(cfg1.runs).toBe(500);
    expect(cfg1.seed).toBe(123);
  });

  it('supports JANUS_PBT_ITERATION override (runs becomes iteration + 1)', () => {
    process.env.JANUS_PBT_RUNS = '999';
    process.env.JANUS_PBT_ITERATION = '42';
    process.env.JANUS_PBT_SEED = '123';
    const cfg = pbtConfig();
    expect(cfg.seed).toBe(123);
    expect(cfg.runs).toBe(43);
  });

  it('clamps runs and ignores invalid seed/run values', () => {
    process.env.JANUS_PBT_RUNS = '0';
    process.env.JANUS_PBT_SEED = 'nope';
    const cfg = pbtConfig();
    expect(cfg.runs).toBe(1);
    expect(Number.isInteger(cfg.seed)).toBe(true);
  });

  it('treats empty/whitespace env vars as unset and falls back', () => {
    process.env.JANUS_PBT_PROFILE = '  ';
    process.env.JANUS_PBT_RUNS = '   ';
    process.env.JANUS_PBT_SEED = '';
    process.env.JANUS_PBT_ITERATION = '   ';
    const cfg = pbtConfig();
    expect(cfg.runs).toBe(250);
    expect(Number.isInteger(cfg.seed)).toBe(true);
  });

  it('ignores non-finite numeric env values (NaN)', () => {
    process.env.JANUS_PBT_PROFILE = 'short';
    process.env.JANUS_PBT_RUNS = 'not-a-number';
    const cfg = pbtConfig();
    expect(cfg.runs).toBe(250);
  });
});


