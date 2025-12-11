import { ContiguousDomainGenerator } from '@/com/techlloyd/janus/domains/ContiguousDomainGenerator';
import { ContiguousDomain, DomainType, ContiguousType } from '@/com/techlloyd/janus/Domain';
import { RNG } from '@/com/techlloyd/janus/RNG';

describe('ContiguousDomainGenerator', () => {
  describe('integer generation', () => {
    it('should generate integers within range', () => {
      const generator = new ContiguousDomainGenerator();
      const domain: ContiguousDomain = {
        type: DomainType.CONTIGUOUS_DOMAIN,
        contiguousType: ContiguousType.INTEGER,
        min: 0,
        max: 10,
      };
      const rng: RNG = {
        random: () => Math.random(),
      };

      for (let i = 0; i < 100; i++) {
        const value = generator.generate(domain, rng);
        expect(Number.isInteger(value)).toBe(true);
        expect(value).toBeGreaterThanOrEqual(0);
        expect(value).toBeLessThanOrEqual(10);
      }
    });

    it('should generate minimum value when RNG returns 0', () => {
      const generator = new ContiguousDomainGenerator();
      const domain: ContiguousDomain = {
        type: DomainType.CONTIGUOUS_DOMAIN,
        contiguousType: ContiguousType.INTEGER,
        min: 5,
        max: 15,
      };
      const rng: RNG = {
        random: () => 0.0,
      };

      const value = generator.generate(domain, rng);
      expect(value).toBe(5);
    });

    it('should generate maximum value when RNG returns close to 1', () => {
      const generator = new ContiguousDomainGenerator();
      const domain: ContiguousDomain = {
        type: DomainType.CONTIGUOUS_DOMAIN,
        contiguousType: ContiguousType.INTEGER,
        min: 5,
        max: 15,
      };
      const rng: RNG = {
        random: () => 0.99999,
      };

      const value = generator.generate(domain, rng);
      expect(value).toBe(15);
    });

    it('should generate negative integers', () => {
      const generator = new ContiguousDomainGenerator();
      const domain: ContiguousDomain = {
        type: DomainType.CONTIGUOUS_DOMAIN,
        contiguousType: ContiguousType.INTEGER,
        min: -10,
        max: -1,
      };
      const rng: RNG = {
        random: () => Math.random(),
      };

      for (let i = 0; i < 50; i++) {
        const value = generator.generate(domain, rng);
        expect(Number.isInteger(value)).toBe(true);
        expect(value).toBeGreaterThanOrEqual(-10);
        expect(value).toBeLessThanOrEqual(-1);
      }
    });

    it('should generate all values in small range', () => {
      const generator = new ContiguousDomainGenerator();
      const domain: ContiguousDomain = {
        type: DomainType.CONTIGUOUS_DOMAIN,
        contiguousType: ContiguousType.INTEGER,
        min: 0,
        max: 3,
      };
      const rng: RNG = {
        random: () => Math.random(),
      };

      const generatedValues = new Set<number>();
      for (let i = 0; i < 500; i++) {
        generatedValues.add(generator.generate(domain, rng));
      }

      expect(generatedValues.has(0)).toBe(true);
      expect(generatedValues.has(1)).toBe(true);
      expect(generatedValues.has(2)).toBe(true);
      expect(generatedValues.has(3)).toBe(true);
    });

    it('should handle single value range', () => {
      const generator = new ContiguousDomainGenerator();
      const domain: ContiguousDomain = {
        type: DomainType.CONTIGUOUS_DOMAIN,
        contiguousType: ContiguousType.INTEGER,
        min: 42,
        max: 42,
      };
      const rng: RNG = {
        random: () => Math.random(),
      };

      for (let i = 0; i < 10; i++) {
        const value = generator.generate(domain, rng);
        expect(value).toBe(42);
      }
    });
  });

  describe('floating point generation', () => {
    it('should generate floats within range', () => {
      const generator = new ContiguousDomainGenerator();
      const domain: ContiguousDomain = {
        type: DomainType.CONTIGUOUS_DOMAIN,
        contiguousType: ContiguousType.FLOAT,
        min: 0,
        max: 1,
      };
      const rng: RNG = {
        random: () => Math.random(),
      };

      for (let i = 0; i < 100; i++) {
        const value = generator.generate(domain, rng);
        expect(value).toBeGreaterThanOrEqual(0);
        expect(value).toBeLessThanOrEqual(1);
      }
    });

    it('should generate minimum value when RNG returns 0', () => {
      const generator = new ContiguousDomainGenerator();
      const domain: ContiguousDomain = {
        type: DomainType.CONTIGUOUS_DOMAIN,
        contiguousType: ContiguousType.FLOAT,
        min: 10,
        max: 20,
      };
      const rng: RNG = {
        random: () => 0.0,
      };

      const value = generator.generate(domain, rng);
      expect(value).toBe(10);
    });

    it('should scale to range correctly', () => {
      const generator = new ContiguousDomainGenerator();
      const domain: ContiguousDomain = {
        type: DomainType.CONTIGUOUS_DOMAIN,
        contiguousType: ContiguousType.FLOAT,
        min: 100,
        max: 200,
      };
      const rng: RNG = {
        random: () => 0.5,
      };

      const value = generator.generate(domain, rng);
      expect(value).toBe(150);
    });
  });

  it('should use strategy from contiguousType directly', () => {
    const generator = new ContiguousDomainGenerator();
    const domain: ContiguousDomain = {
      type: DomainType.CONTIGUOUS_DOMAIN,
      contiguousType: ContiguousType.INTEGER,
      min: 0,
      max: 10,
    };
    const rng: RNG = {
      random: () => 0.5,
    };

    // Verify the strategy is accessed directly from contiguousType
    expect(domain.contiguousType.strategy).toBeDefined();
    const value = generator.generate(domain, rng);
    expect(Number.isInteger(value)).toBe(true);
  });
});

