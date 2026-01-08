import { CharClass, CharClasses, charRange, CharRange } from '@/com/techlloyd/janus/combinators/regex/CharClass';
import { DomainType } from '@/com/techlloyd/janus/Domain';
import { RNG } from '@/com/techlloyd/janus/RNG';
import { Generator } from '@/com/techlloyd/janus/Generator';

describe('CharClass', () => {
  describe('matching', () => {
    it('should match any character in the class', () => {
      const charClass = new CharClass([charRange('a', 'c')]);
      expect(charClass.match('a', 0).matched).toBe(true);
      expect(charClass.match('b', 0).matched).toBe(true);
      expect(charClass.match('c', 0).matched).toBe(true);
    });

    it('should not match characters outside the class', () => {
      const charClass = new CharClass([charRange('a', 'c')]);
      expect(charClass.match('d', 0).matched).toBe(false);
      expect(charClass.match('x', 0).matched).toBe(false);
    });

    it('should consume exactly 1 character', () => {
      const charClass = new CharClass([charRange('a', 'c')]);
      const result = charClass.match('abc', 0);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(1);
    });

    it('should match at any position', () => {
      const charClass = new CharClass([charRange('x', 'z')]);
      expect(charClass.match('axyz', 1).matched).toBe(true);
      expect(charClass.match('axyz', 2).matched).toBe(true);
    });

    it('should not match past end of string', () => {
      const charClass = new CharClass([charRange('a', 'b')]);
      expect(charClass.match('ab', 2).matched).toBe(false);
    });
  });

  describe('negated classes', () => {
    it('should fail fast for unsupported negated character classes', () => {
      expect(() => new CharClass([charRange('0', '9')], true)).toThrow('Unsupported regex construct');
    });
  });

  describe('validation', () => {
    it('should validate single character from class', () => {
      const charClass = new CharClass([charRange('a', 'c')]);
      expect(charClass.validate('a').valid).toBe(true);
      expect(charClass.validate('b').valid).toBe(true);
    });

    it('should reject longer strings', () => {
      const charClass = new CharClass([charRange('a', 'c')]);
      expect(charClass.validate('ab').valid).toBe(false);
    });

    it('should reject empty strings', () => {
      const charClass = new CharClass([charRange('a', 'c')]);
      expect(charClass.validate('').valid).toBe(false);
    });

    it('should reject non-strings', () => {
      const charClass = new CharClass([charRange('a', 'c')]);
      expect(charClass.validate(123).valid).toBe(false);
    });
  });

  describe('generation', () => {
    it('should generate characters from the class', () => {
      const charClass = new CharClass([charRange('a', 'c')]);
      const rng: RNG = { random: () => Math.random() };
      const generator = new Generator(rng);

      const generated = new Set<string>();
      for (let i = 0; i < 100; i++) {
        const value = generator.generate(charClass.domain);
        expect(['a', 'b', 'c']).toContain(value);
        generated.add(value);
      }
      // Should generate variety
      expect(generated.size).toBeGreaterThan(1);
    });

    it('should select specific character based on RNG', () => {
      const charClass = new CharClass([charRange('x', 'z')]);
      
      // RNG 0 should select first character
      expect(new Generator({ random: () => 0.0 }).generate(charClass.domain)).toBe('x');
      // RNG close to 1 should select last character
      expect(new Generator({ random: () => 0.99 }).generate(charClass.domain)).toBe('z');
    });
  });

  describe('domain', () => {
    it('should expose a regex domain', () => {
      const charClass = new CharClass([charRange('a', 'c')]);
      expect(charClass.domain.kind).toBe(DomainType.REGEX);
      expect(charClass.domain.source).toBe('[a-c]');
    });
  });
});

describe('CharClasses factory', () => {
  describe('digit()', () => {
    it('should match digits 0-9', () => {
      const digit = CharClasses.digit();
      for (let i = 0; i <= 9; i++) {
        expect(digit.match(String(i), 0).matched).toBe(true);
      }
    });

    it('should not match non-digits', () => {
      const digit = CharClasses.digit();
      expect(digit.match('a', 0).matched).toBe(false);
      expect(digit.match('!', 0).matched).toBe(false);
    });
  });

  describe('word()', () => {
    it('should match word characters [a-zA-Z0-9_]', () => {
      const word = CharClasses.word();
      expect(word.match('a', 0).matched).toBe(true);
      expect(word.match('Z', 0).matched).toBe(true);
      expect(word.match('5', 0).matched).toBe(true);
      expect(word.match('_', 0).matched).toBe(true);
    });

    it('should not match non-word characters', () => {
      const word = CharClasses.word();
      expect(word.match('!', 0).matched).toBe(false);
      expect(word.match(' ', 0).matched).toBe(false);
      expect(word.match('-', 0).matched).toBe(false);
    });
  });

  describe('whitespace()', () => {
    it('should match whitespace characters', () => {
      const ws = CharClasses.whitespace();
      expect(ws.match(' ', 0).matched).toBe(true);
      expect(ws.match('\t', 0).matched).toBe(true);
      expect(ws.match('\n', 0).matched).toBe(true);
    });

    it('should not match non-whitespace', () => {
      const ws = CharClasses.whitespace();
      expect(ws.match('a', 0).matched).toBe(false);
      expect(ws.match('1', 0).matched).toBe(false);
    });
  });

  describe('range()', () => {
    it('should create a range of characters', () => {
      const range = CharClasses.range('a', 'f');
      expect(range.match('a', 0).matched).toBe(true);
      expect(range.match('c', 0).matched).toBe(true);
      expect(range.match('f', 0).matched).toBe(true);
      expect(range.match('g', 0).matched).toBe(false);
    });
  });
});
