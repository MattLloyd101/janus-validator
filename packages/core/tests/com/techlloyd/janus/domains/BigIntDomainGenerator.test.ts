import { BigIntDomainGenerator } from '@/com/techlloyd/janus/domains/BigIntDomainGenerator';
import { DomainType, type BigIntDomain } from '@/com/techlloyd/janus/Domain';
import { rngFromSequence } from './helpers';

describe('BigIntDomainGenerator', () => {
  it('should generate within small ranges (uses simple branch)', () => {
    const generator = new BigIntDomainGenerator();
    const domain: BigIntDomain = {
      type: DomainType.BIGINT_DOMAIN,
      min: 0n,
      max: 9n,
    };

    // range=10, offset=floor(0.5*10)=5
    const value = generator.generate(domain, rngFromSequence([0.5]));
    expect(value).toBe(5n);
  });

  it('should generate within large ranges (uses byte-scaling branch)', () => {
    const generator = new BigIntDomainGenerator();

    // range > Number.MAX_SAFE_INTEGER to force the large-range branch
    const max = BigInt(Number.MAX_SAFE_INTEGER) + 100n;
    const domain: BigIntDomain = {
      type: DomainType.BIGINT_DOMAIN,
      min: 0n,
      max,
    };

    // Provide zeros so the constructed bigint is 0n and passes rejection sampling immediately.
    const value = generator.generate(domain, rngFromSequence(Array(32).fill(0)));
    expect(value).toBeGreaterThanOrEqual(0n);
    expect(value).toBeLessThanOrEqual(max);
  });
});


