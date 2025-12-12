import { BytesDomainGenerator } from '@/com/techlloyd/janus/domains/BytesDomainGenerator';
import { DomainType, type BytesDomain } from '@/com/techlloyd/janus/Domain';
import { rngFromSequence } from './helpers';

describe('BytesDomainGenerator', () => {
  it('should generate fixed-length bytes when minLength=maxLength', () => {
    const generator = new BytesDomainGenerator();
    const domain: BytesDomain = {
      type: DomainType.BYTES_DOMAIN,
      minLength: 4,
      maxLength: 4,
    };

    // rng[0] chooses length (fixed anyway), remaining choose bytes -> all zeros
    const value = generator.generate(domain, rngFromSequence([0, 0, 0, 0, 0]));
    expect(value).toBeInstanceOf(Uint8Array);
    expect(value.length).toBe(4);
    expect(Array.from(value)).toEqual([0, 0, 0, 0]);
  });

  it('should generate length within range', () => {
    const generator = new BytesDomainGenerator();
    const domain: BytesDomain = {
      type: DomainType.BYTES_DOMAIN,
      minLength: 1,
      maxLength: 3,
    };

    // length = 1 + floor(0.99 * (3)) = 3
    const value = generator.generate(domain, rngFromSequence([0.99, 0, 0, 0, 0]));
    expect(value.length).toBe(3);
  });
});


