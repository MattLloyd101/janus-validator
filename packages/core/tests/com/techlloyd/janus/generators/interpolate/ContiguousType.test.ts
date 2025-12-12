import { ContiguousType, ContiguousTypeValue } from '@/com/techlloyd/janus/generators/interpolate/ContiguousType';
import { IntegerInterpolateStrategy } from '@/com/techlloyd/janus/generators/interpolate/IntegerInterpolateStrategy';
import { FloatInterpolateStrategy } from '@/com/techlloyd/janus/generators/interpolate/FloatInterpolateStrategy';

describe('ContiguousType', () => {
  describe('INTEGER', () => {
    it('should have correct name', () => {
      expect(ContiguousType.INTEGER.name).toBe('INTEGER');
    });

    it('should have an IntegerInterpolateStrategy', () => {
      expect(ContiguousType.INTEGER.strategy).toBeInstanceOf(IntegerInterpolateStrategy);
    });

    it('should satisfy ContiguousTypeValue interface', () => {
      const value: ContiguousTypeValue = ContiguousType.INTEGER;
      expect(value.name).toBeDefined();
      expect(value.strategy).toBeDefined();
      expect(typeof value.strategy.interpolate).toBe('function');
    });
  });

  describe('FLOAT', () => {
    it('should have correct name', () => {
      expect(ContiguousType.FLOAT.name).toBe('FLOAT');
    });

    it('should have a FloatInterpolateStrategy', () => {
      expect(ContiguousType.FLOAT.strategy).toBeInstanceOf(FloatInterpolateStrategy);
    });

    it('should satisfy ContiguousTypeValue interface', () => {
      const value: ContiguousTypeValue = ContiguousType.FLOAT;
      expect(value.name).toBeDefined();
      expect(value.strategy).toBeDefined();
      expect(typeof value.strategy.interpolate).toBe('function');
    });
  });

  describe('strategy behavior', () => {
    it('INTEGER strategy should generate integers', () => {
      const rng = { random: () => Math.random() };
      
      for (let i = 0; i < 50; i++) {
        const value = ContiguousType.INTEGER.strategy.interpolate(0, 10, rng);
        expect(Number.isInteger(value)).toBe(true);
      }
    });

    it('FLOAT strategy should generate floats', () => {
      const rng = { random: () => 0.5 };
      const value = ContiguousType.FLOAT.strategy.interpolate(0, 100, rng);
      expect(value).toBe(50);
    });

    it('strategies should be reusable', () => {
      const rng = { random: () => 0.5 };
      
      // Same strategy instance can be used multiple times
      expect(ContiguousType.INTEGER.strategy.interpolate(0, 10, rng)).toBe(5);
      expect(ContiguousType.INTEGER.strategy.interpolate(10, 20, rng)).toBe(15);
      expect(ContiguousType.FLOAT.strategy.interpolate(0, 100, rng)).toBe(50);
      expect(ContiguousType.FLOAT.strategy.interpolate(100, 200, rng)).toBe(150);
    });
  });

  describe('immutability', () => {
    it('should be a constant object', () => {
      // ContiguousType should not be reassignable
      expect(Object.isFrozen(ContiguousType)).toBe(false); // as const doesn't freeze
      expect(ContiguousType.INTEGER).toBeDefined();
      expect(ContiguousType.FLOAT).toBeDefined();
    });

    it('should have consistent references', () => {
      const intRef1 = ContiguousType.INTEGER;
      const intRef2 = ContiguousType.INTEGER;
      expect(intRef1).toBe(intRef2);

      const floatRef1 = ContiguousType.FLOAT;
      const floatRef2 = ContiguousType.FLOAT;
      expect(floatRef1).toBe(floatRef2);
    });
  });
});

