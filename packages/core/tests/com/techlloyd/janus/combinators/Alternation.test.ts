import { Alternation } from '@/com/techlloyd/janus/combinators/Alternation';
import { Boolean } from '@/com/techlloyd/janus/combinators/Boolean';
import { Integer } from '@/com/techlloyd/janus/combinators/Integer';
import { Generator, RNG, DomainType } from '@/com/techlloyd/janus/index';

describe('Generic Alternation combinator', () => {
  describe('validation', () => {
    it('should validate values matching any alternative', () => {
      const alt = new Alternation(
        Integer(0, 10),
        Integer(100, 200)
      );
      
      expect(alt.validate(5).valid).toBe(true);
      expect(alt.validate(150).valid).toBe(true);
    });

    it('should reject values not matching any alternative', () => {
      const alt = new Alternation(
        Integer(0, 10),
        Integer(100, 200)
      );
      
      expect(alt.validate(50).valid).toBe(false);
      expect(alt.validate(250).valid).toBe(false);
    });

    it('should work with different validator types', () => {
      const alt = new Alternation<boolean | number>(
        Boolean(),
        Integer(0, 100)
      );
      
      expect(alt.validate(true).valid).toBe(true);
      expect(alt.validate(false).valid).toBe(true);
      expect(alt.validate(50).valid).toBe(true);
      expect(alt.validate('hello').valid).toBe(false);
    });

    it('should return first matching result', () => {
      const alt = new Alternation(
        Integer(0, 100),
        Integer(50, 150)
      );
      
      // 75 matches both, should return success from first
      const result = alt.validate(75);
      expect(result.valid).toBe(true);
    });

    it('should provide meaningful error messages', () => {
      const alt = new Alternation(
        Integer(0, 10),
        Integer(100, 200)
      );
      
      const result = alt.validate(50);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('did not match any alternative');
      }
    });

    it('should reject non-matching types', () => {
      const alt = new Alternation(Integer(0, 10));
      
      expect(alt.validate('hello').valid).toBe(false);
      expect(alt.validate(null).valid).toBe(false);
      expect(alt.validate(undefined).valid).toBe(false);
    });
  });

  describe('domain', () => {
    it('should expose an alternation domain', () => {
      const alt = new Alternation(
        Integer(0, 10),
        Integer(100, 200)
      );
      
      expect(alt.domain.type).toBe(DomainType.ALTERNATION_DOMAIN);
      expect(alt.domain.alternatives).toHaveLength(2);
    });

    it('should contain child domains', () => {
      const int1 = Integer(0, 10);
      const int2 = Integer(100, 200);
      const alt = new Alternation(int1, int2);
      
      expect(alt.domain.alternatives[0]).toBe(int1.domain);
      expect(alt.domain.alternatives[1]).toBe(int2.domain);
    });
  });

  describe('generation', () => {
    it('should generate values from any alternative', () => {
      const alt = new Alternation(
        Integer(0, 10),
        Integer(100, 200)
      );
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 100; i++) {
        const value = generator.generate(alt.domain) as number;
        expect(typeof value).toBe('number');
        // Should be in one of the two ranges
        const inFirstRange = value >= 0 && value <= 10;
        const inSecondRange = value >= 100 && value <= 200;
        expect(inFirstRange || inSecondRange).toBe(true);
      }
    });

    it('should generate variety across alternatives', () => {
      const alt = new Alternation(
        Integer(0, 10),
        Integer(100, 200)
      );
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      let foundFirst = false;
      let foundSecond = false;

      for (let i = 0; i < 100; i++) {
        const value = generator.generate(alt.domain) as number;
        if (value >= 0 && value <= 10) foundFirst = true;
        if (value >= 100 && value <= 200) foundSecond = true;
      }

      expect(foundFirst).toBe(true);
      expect(foundSecond).toBe(true);
    });

    it('should generate values that pass validation', () => {
      const alt = new Alternation(
        Integer(0, 10),
        Integer(100, 200)
      );
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      for (let i = 0; i < 100; i++) {
        const value = generator.generate(alt.domain);
        const result = alt.validate(value);
        expect(result.valid).toBe(true);
      }
    });
  });

  describe('Alternation.of factory', () => {
    it('should throw for empty array', () => {
      expect(() => Alternation.of()).toThrow();
    });

    it('should return single validator for single element', () => {
      const int = Integer(0, 10);
      const result = Alternation.of(int);
      expect(result).toBe(int);
    });

    it('should create Alternation for multiple validators', () => {
      const result = Alternation.of(Integer(0, 10), Integer(100, 200));
      expect(result).toBeInstanceOf(Alternation);
    });
  });

  describe('complex examples', () => {
    it('should work with nested alternations', () => {
      const inner = new Alternation(Integer(0, 10), Integer(20, 30));
      const outer = new Alternation(inner, Integer(100, 200));
      
      expect(outer.validate(5).valid).toBe(true);
      expect(outer.validate(25).valid).toBe(true);
      expect(outer.validate(150).valid).toBe(true);
      expect(outer.validate(50).valid).toBe(false);
    });

    it('should work with boolean alternation', () => {
      const alt = new Alternation(Boolean());
      
      expect(alt.validate(true).valid).toBe(true);
      expect(alt.validate(false).valid).toBe(true);
      expect(alt.validate(1).valid).toBe(false);
    });
  });
});

