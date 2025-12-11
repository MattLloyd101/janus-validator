import { CharClass, CharClasses } from '@/com/techlloyd/janus/combinators/regex/CharClass';
import { DomainType } from '@/com/techlloyd/janus/Domain';
import { RNG } from '@/com/techlloyd/janus/RNG';

describe('CharClass', () => {
  describe('matching', () => {
    it('should match any character in the class', () => {
      const charClass = new CharClass(['a', 'b', 'c']);
      expect(charClass.match('a', 0).matched).toBe(true);
      expect(charClass.match('b', 0).matched).toBe(true);
      expect(charClass.match('c', 0).matched).toBe(true);
    });

    it('should not match characters outside the class', () => {
      const charClass = new CharClass(['a', 'b', 'c']);
      expect(charClass.match('d', 0).matched).toBe(false);
      expect(charClass.match('x', 0).matched).toBe(false);
    });

    it('should consume exactly 1 character', () => {
      const charClass = new CharClass(['a', 'b', 'c']);
      const result = charClass.match('abc', 0);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(1);
    });

    it('should match at any position', () => {
      const charClass = new CharClass(['x', 'y', 'z']);
      expect(charClass.match('axyz', 1).matched).toBe(true);
      expect(charClass.match('axyz', 2).matched).toBe(true);
    });

    it('should not match past end of string', () => {
      const charClass = new CharClass(['a', 'b']);
      expect(charClass.match('ab', 2).matched).toBe(false);
    });
  });

  describe('negated matching', () => {
    it('should match characters NOT in the negated class', () => {
      const negatedClass = new CharClass(['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'], true);
      expect(negatedClass.match('a', 0).matched).toBe(true);
      expect(negatedClass.match('Z', 0).matched).toBe(true);
      expect(negatedClass.match('!', 0).matched).toBe(true);
    });

    it('should NOT match characters in the negated class', () => {
      const negatedClass = new CharClass(['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'], true);
      expect(negatedClass.match('0', 0).matched).toBe(false);
      expect(negatedClass.match('5', 0).matched).toBe(false);
      expect(negatedClass.match('9', 0).matched).toBe(false);
    });
  });

  describe('validation', () => {
    it('should validate single character from class', () => {
      const charClass = new CharClass(['a', 'b', 'c']);
      expect(charClass.validate('a').valid).toBe(true);
      expect(charClass.validate('b').valid).toBe(true);
    });

    it('should reject longer strings', () => {
      const charClass = new CharClass(['a', 'b', 'c']);
      expect(charClass.validate('ab').valid).toBe(false);
    });

    it('should reject empty strings', () => {
      const charClass = new CharClass(['a', 'b', 'c']);
      expect(charClass.validate('').valid).toBe(false);
    });

    it('should reject non-strings', () => {
      const charClass = new CharClass(['a', 'b', 'c']);
      expect(charClass.validate(123).valid).toBe(false);
    });
  });

  describe('generation', () => {
    it('should generate characters from the class', () => {
      const charClass = new CharClass(['a', 'b', 'c']);
      const rng: RNG = { random: () => Math.random() };

      const generated = new Set<string>();
      for (let i = 0; i < 100; i++) {
        const value = charClass.generate(rng);
        expect(['a', 'b', 'c']).toContain(value);
        generated.add(value);
      }
      // Should generate variety
      expect(generated.size).toBeGreaterThan(1);
    });

    it('should generate from negated class', () => {
      const negatedClass = new CharClass(['a', 'b', 'c'], true);
      const rng: RNG = { random: () => Math.random() };

      for (let i = 0; i < 50; i++) {
        const value = negatedClass.generate(rng);
        expect(value).not.toBe('a');
        expect(value).not.toBe('b');
        expect(value).not.toBe('c');
      }
    });

    it('should select specific character based on RNG', () => {
      const charClass = new CharClass(['x', 'y', 'z']);
      
      // RNG 0 should select first character
      expect(charClass.generate({ random: () => 0.0 })).toBe('x');
      // RNG close to 1 should select last character
      expect(charClass.generate({ random: () => 0.99 })).toBe('z');
    });
  });

  describe('domain', () => {
    it('should expose a regex domain', () => {
      const charClass = new CharClass(['a', 'b', 'c']);
      expect(charClass.domain.type).toBe(DomainType.REGEX_DOMAIN);
      expect(charClass.domain.source).toBe('[abc]');
    });

    it('should format negated class correctly', () => {
      const negatedClass = new CharClass(['a', 'b'], true);
      expect(negatedClass.domain.source).toBe('[^ab]');
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

  describe('nonDigit()', () => {
    it('should NOT match digits', () => {
      const nonDigit = CharClasses.nonDigit();
      for (let i = 0; i <= 9; i++) {
        expect(nonDigit.match(String(i), 0).matched).toBe(false);
      }
    });

    it('should match non-digits', () => {
      const nonDigit = CharClasses.nonDigit();
      expect(nonDigit.match('a', 0).matched).toBe(true);
      expect(nonDigit.match('!', 0).matched).toBe(true);
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

