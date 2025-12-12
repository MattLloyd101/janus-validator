import {
  withGenerator,
  fromValues,
  fromWeightedValues,
  cycleValues,
  combineGenerators,
  templateGenerator,
} from '@/com/techlloyd/janus/combinators/WithGenerator';
import { UnicodeString } from '@/com/techlloyd/janus/combinators/UnicodeString';
import { Integer } from '@/com/techlloyd/janus/combinators/Integer';
import { Generator } from '@/com/techlloyd/janus/Generator';
import { RNG } from '@/com/techlloyd/janus/RNG';
import { DomainType } from '@/com/techlloyd/janus/Domain';

class DefaultRNG implements RNG {
  random(): number {
    return Math.random();
  }
}

class SeededRNG implements RNG {
  private value: number;
  
  constructor(seed: number) {
    this.value = seed;
  }
  
  random(): number {
    return this.value;
  }
}

describe('withGenerator', () => {
  const rng = new DefaultRNG();
  
  it('should override generation while preserving validation', () => {
    const names = ['Alice', 'Bob', 'Charlie'];
    const validator = withGenerator(
      UnicodeString(1, 50),
      (rng) => names[Math.floor(rng.random() * names.length)]
    );

    // Validation still works
    expect(validator.validate('Alice').valid).toBe(true);
    expect(validator.validate('SomeOtherName').valid).toBe(true);
    expect(validator.validate('').valid).toBe(false); // too short

    // Generation uses custom logic
    const generator = new Generator(rng);
    for (let i = 0; i < 20; i++) {
      const value = generator.generate(validator.domain);
      expect(names).toContain(value);
    }
  });

  it('should expose CUSTOM_GENERATOR_DOMAIN type', () => {
    const validator = withGenerator(UnicodeString(), () => 'test');
    expect(validator.domain.type).toBe(DomainType.CUSTOM_GENERATOR_DOMAIN);
  });

  it('should preserve inner domain', () => {
    const original = UnicodeString(5, 10);
    const custom = withGenerator(original, () => 'hello');
    
    expect((custom.domain as any).innerDomain).toBe(original.domain);
  });
});

describe('fromValues', () => {
  const rng = new DefaultRNG();

  it('should generate only from the provided values', () => {
    const values = ['red', 'green', 'blue'];
    const validator = fromValues(UnicodeString(), values);

    const generator = new Generator(rng);
    const generated = new Set<string>();
    
    for (let i = 0; i < 50; i++) {
      const value = generator.generate(validator.domain);
      expect(values).toContain(value);
      generated.add(value);
    }

    // Should eventually generate all values
    expect(generated.size).toBe(3);
  });

  it('should throw for empty values array', () => {
    expect(() => fromValues(UnicodeString(), [])).toThrow();
  });

  it('should validate against original validator', () => {
    const validator = fromValues(UnicodeString(1, 5), ['cat', 'dog']);
    
    expect(validator.validate('cat').valid).toBe(true);
    expect(validator.validate('').valid).toBe(false);
    expect(validator.validate('elephant').valid).toBe(false);
  });
});

describe('fromWeightedValues', () => {
  it('should generate values with approximate weights', () => {
    const validator = fromWeightedValues(UnicodeString(), [
      ['common', 0.9],
      ['rare', 0.1],
    ]);

    const rng = new DefaultRNG();
    const generator = new Generator(rng);
    
    let commonCount = 0;
    let rareCount = 0;
    const iterations = 1000;

    for (let i = 0; i < iterations; i++) {
      const value = generator.generate(validator.domain);
      if (value === 'common') commonCount++;
      if (value === 'rare') rareCount++;
    }

    // Allow some variance but common should be much more frequent
    expect(commonCount).toBeGreaterThan(rareCount * 5);
  });

  it('should throw for empty weighted values', () => {
    expect(() => fromWeightedValues(UnicodeString(), [])).toThrow();
  });

  it('should select based on RNG value', () => {
    const validator = fromWeightedValues(UnicodeString(), [
      ['first', 0.3],
      ['second', 0.3],
      ['third', 0.4],
    ]);

    // RNG returning 0 should select first value
    expect(new Generator(new SeededRNG(0)).generate(validator.domain)).toBe('first');
    
    // RNG returning 0.5 should select second (0.3 + 0.2 into second)
    expect(new Generator(new SeededRNG(0.5)).generate(validator.domain)).toBe('second');
    
    // RNG returning 0.9 should select third
    expect(new Generator(new SeededRNG(0.9)).generate(validator.domain)).toBe('third');
  });
});

describe('cycleValues', () => {
  it('should cycle through values in order', () => {
    const values = ['A', 'B', 'C'];
    const validator = cycleValues(UnicodeString(), values);

    const rng = new DefaultRNG();
    const generator = new Generator(rng);

    expect(generator.generate(validator.domain)).toBe('A');
    expect(generator.generate(validator.domain)).toBe('B');
    expect(generator.generate(validator.domain)).toBe('C');
    expect(generator.generate(validator.domain)).toBe('A'); // wraps around
    expect(generator.generate(validator.domain)).toBe('B');
  });

  it('should throw for empty values', () => {
    expect(() => cycleValues(UnicodeString(), [])).toThrow();
  });
});

describe('combineGenerators', () => {
  it('should randomly select from multiple generators', () => {
    const validator = combineGenerators(Integer(0, 1000), [
      () => 100,
      () => 200,
      () => 300,
    ]);

    const rng = new DefaultRNG();
    const generator = new Generator(rng);
    
    const generated = new Set<number>();
    for (let i = 0; i < 50; i++) {
      generated.add(generator.generate(validator.domain));
    }

    // Should generate variety
    expect(generated.size).toBe(3);
    expect(generated).toContain(100);
    expect(generated).toContain(200);
    expect(generated).toContain(300);
  });

  it('should throw for empty generators', () => {
    expect(() => combineGenerators(UnicodeString(), [])).toThrow();
  });
});

describe('templateGenerator', () => {
  it('should generate strings using the template', () => {
    const adjectives = ['happy', 'sad', 'clever'];
    const nouns = ['cat', 'dog', 'bird'];

    const validator = templateGenerator(UnicodeString(), (pick) => {
      return `${pick(adjectives)}_${pick(nouns)}`;
    });

    const rng = new DefaultRNG();
    const generator = new Generator(rng);

    for (let i = 0; i < 20; i++) {
      const value = generator.generate(validator.domain);
      const parts = value.split('_');
      expect(adjectives).toContain(parts[0]);
      expect(nouns).toContain(parts[1]);
    }
  });

  it('should pass RNG to template', () => {
    const validator = templateGenerator(UnicodeString(), (pick, rng) => {
      return `value_${Math.floor(rng.random() * 100)}`;
    });

    const rng = new DefaultRNG();
    const generator = new Generator(rng);
    
    // Generate multiple values - they should all match pattern
    for (let i = 0; i < 10; i++) {
      const value = generator.generate(validator.domain);
      expect(value).toMatch(/^value_\d+$/);
    }
  });
});

describe('Integration with Generator class', () => {
  it('should surface examples via BaseValidator error helpers', () => {
    const validator = fromValues(UnicodeString(1, 10), ['Alice', 'Bob', 'Charlie']);

    // Validation failure should include example from custom generator
    const result = validator.validate('');
    expect(result.valid).toBe(false);
    if (!result.valid) {
      expect(['Alice', 'Bob', 'Charlie']).toContain(result.example);
    }
  });
});

