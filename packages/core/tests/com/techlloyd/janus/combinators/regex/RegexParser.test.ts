import { parseRegex } from '@/com/techlloyd/janus/combinators/regex/RegexParser';
import { RNG } from '@/com/techlloyd/janus/RNG';

describe('RegexParser', () => {
  const rng: RNG = { random: () => Math.random() };

  describe('literals', () => {
    it('should parse single literal', () => {
      const validator = parseRegex('a');
      expect(validator.match('a', 0).matched).toBe(true);
      expect(validator.match('b', 0).matched).toBe(false);
    });

    it('should parse literal sequence', () => {
      const validator = parseRegex('abc');
      expect(validator.match('abc', 0).matched).toBe(true);
      expect(validator.match('abd', 0).matched).toBe(false);
    });

    it('should parse escaped special characters', () => {
      const dotValidator = parseRegex('\\.');
      expect(dotValidator.match('.', 0).matched).toBe(true);
      expect(dotValidator.match('a', 0).matched).toBe(false);

      const starValidator = parseRegex('\\*');
      expect(starValidator.match('*', 0).matched).toBe(true);
    });
  });

  describe('character classes', () => {
    it('should parse simple character class', () => {
      const validator = parseRegex('[abc]');
      expect(validator.match('a', 0).matched).toBe(true);
      expect(validator.match('b', 0).matched).toBe(true);
      expect(validator.match('c', 0).matched).toBe(true);
      expect(validator.match('d', 0).matched).toBe(false);
    });

    it('should parse character range', () => {
      const validator = parseRegex('[a-z]');
      expect(validator.match('a', 0).matched).toBe(true);
      expect(validator.match('m', 0).matched).toBe(true);
      expect(validator.match('z', 0).matched).toBe(true);
      expect(validator.match('A', 0).matched).toBe(false);
    });

    it('should parse negated character class', () => {
      const validator = parseRegex('[^abc]');
      expect(validator.match('a', 0).matched).toBe(false);
      expect(validator.match('d', 0).matched).toBe(true);
    });

    it('should parse \\d', () => {
      const validator = parseRegex('\\d');
      for (let i = 0; i <= 9; i++) {
        expect(validator.match(String(i), 0).matched).toBe(true);
      }
      expect(validator.match('a', 0).matched).toBe(false);
    });

    it('should parse \\w', () => {
      const validator = parseRegex('\\w');
      expect(validator.match('a', 0).matched).toBe(true);
      expect(validator.match('Z', 0).matched).toBe(true);
      expect(validator.match('5', 0).matched).toBe(true);
      expect(validator.match('_', 0).matched).toBe(true);
      expect(validator.match('!', 0).matched).toBe(false);
    });

    it('should parse \\s', () => {
      const validator = parseRegex('\\s');
      expect(validator.match(' ', 0).matched).toBe(true);
      expect(validator.match('\t', 0).matched).toBe(true);
      expect(validator.match('a', 0).matched).toBe(false);
    });

    it('should parse \\d inside character class', () => {
      const validator = parseRegex('[\\d]');
      for (let i = 0; i <= 9; i++) {
        expect(validator.match(String(i), 0).matched).toBe(true);
      }
      expect(validator.match('a', 0).matched).toBe(false);
    });

    it('should parse \\s inside character class', () => {
      const validator = parseRegex('[\\s]');
      expect(validator.match(' ', 0).matched).toBe(true);
      expect(validator.match('\t', 0).matched).toBe(true);
      expect(validator.match('a', 0).matched).toBe(false);
    });

    it('should parse \\w inside character class', () => {
      const validator = parseRegex('[\\w]');
      expect(validator.match('a', 0).matched).toBe(true);
      expect(validator.match('Z', 0).matched).toBe(true);
      expect(validator.match('5', 0).matched).toBe(true);
      expect(validator.match('_', 0).matched).toBe(true);
      expect(validator.match('!', 0).matched).toBe(false);
    });

    it('should parse mixed escape and literal in character class', () => {
      // [\d\s-] should match digits, whitespace, and dash
      const validator = parseRegex('[\\d\\s-]');
      expect(validator.match('5', 0).matched).toBe(true);
      expect(validator.match(' ', 0).matched).toBe(true);
      expect(validator.match('-', 0).matched).toBe(true);
      expect(validator.match('a', 0).matched).toBe(false);
    });

    it('should generate from character class with \\d', () => {
      const validator = parseRegex('[\\d]');
      for (let i = 0; i < 20; i++) {
        const value = validator.generate(rng);
        expect(value).toMatch(/^\d$/);
      }
    });

    it('should generate from character class with \\s', () => {
      const validator = parseRegex('[\\s]');
      for (let i = 0; i < 20; i++) {
        const value = validator.generate(rng);
        expect(value).toMatch(/^\s$/);
      }
    });

    it('should generate from mixed character class', () => {
      const validator = parseRegex('[\\d\\s-]');
      for (let i = 0; i < 50; i++) {
        const value = validator.generate(rng);
        expect(value).toMatch(/^[\d\s-]$/);
      }
    });
  });

  describe('quantifiers', () => {
    it('should parse * quantifier', () => {
      const validator = parseRegex('a*');
      expect(validator.match('', 0).matched).toBe(true);
      expect(validator.match('a', 0).matched).toBe(true);
      expect(validator.match('aaa', 0).matched).toBe(true);
    });

    it('should parse + quantifier', () => {
      const validator = parseRegex('a+');
      expect(validator.match('', 0).matched).toBe(false);
      expect(validator.match('a', 0).matched).toBe(true);
      expect(validator.match('aaa', 0).matched).toBe(true);
    });

    it('should parse ? quantifier', () => {
      const validator = parseRegex('a?');
      expect(validator.match('', 0).matched).toBe(true);
      expect(validator.match('a', 0).matched).toBe(true);
      expect(validator.match('aa', 0).consumed).toBe(1);
    });

    it('should parse {n} quantifier', () => {
      const validator = parseRegex('a{3}');
      expect(validator.match('aa', 0).matched).toBe(false);
      expect(validator.match('aaa', 0).matched).toBe(true);
    });

    it('should parse {n,} quantifier', () => {
      const validator = parseRegex('a{2,}');
      expect(validator.match('a', 0).matched).toBe(false);
      expect(validator.match('aa', 0).matched).toBe(true);
      expect(validator.match('aaaa', 0).matched).toBe(true);
    });

    it('should parse {n,m} quantifier', () => {
      const validator = parseRegex('a{2,4}');
      expect(validator.match('a', 0).matched).toBe(false);
      expect(validator.match('aa', 0).matched).toBe(true);
      expect(validator.match('aaaa', 0).matched).toBe(true);
      expect(validator.match('aaaaa', 0).consumed).toBe(4);
    });
  });

  describe('alternation', () => {
    it('should parse simple alternation', () => {
      const validator = parseRegex('a|b|c');
      expect(validator.match('a', 0).matched).toBe(true);
      expect(validator.match('b', 0).matched).toBe(true);
      expect(validator.match('c', 0).matched).toBe(true);
      expect(validator.match('d', 0).matched).toBe(false);
    });

    it('should parse alternation of sequences', () => {
      const validator = parseRegex('cat|dog|bird');
      expect(validator.match('cat', 0).matched).toBe(true);
      expect(validator.match('dog', 0).matched).toBe(true);
      expect(validator.match('bird', 0).matched).toBe(true);
      expect(validator.match('fish', 0).matched).toBe(false);
    });
  });

  describe('groups', () => {
    it('should parse capturing group', () => {
      const validator = parseRegex('(abc)');
      expect(validator.match('abc', 0).matched).toBe(true);
    });

    it('should parse non-capturing group', () => {
      const validator = parseRegex('(?:abc)');
      expect(validator.match('abc', 0).matched).toBe(true);
    });

    it('should parse group with quantifier', () => {
      const validator = parseRegex('(ab)+');
      expect(validator.match('ab', 0).matched).toBe(true);
      expect(validator.match('abab', 0).matched).toBe(true);
      expect(validator.match('a', 0).matched).toBe(false);
    });

    it('should parse nested groups', () => {
      const validator = parseRegex('((a)(b))');
      expect(validator.match('ab', 0).matched).toBe(true);
    });
  });

  describe('anchors', () => {
    it('should parse ^ anchor', () => {
      const validator = parseRegex('^a');
      expect(validator.match('a', 0).matched).toBe(true);
      expect(validator.match('ba', 1).matched).toBe(false);
    });

    it('should parse $ anchor', () => {
      const validator = parseRegex('a$');
      // $ matches at end, so 'a' at position 0 with $ at position 1 (end) should match
      expect(validator.validate('a').valid).toBe(true);
    });

    it('should parse \\b anchor', () => {
      const validator = parseRegex('\\b');
      // Word boundary at start of word
      expect(validator.match('hello', 0).matched).toBe(true);
    });
  });

  describe('any character (.)', () => {
    it('should parse . to match any character', () => {
      const validator = parseRegex('.');
      expect(validator.match('a', 0).matched).toBe(true);
      expect(validator.match('5', 0).matched).toBe(true);
      expect(validator.match('!', 0).matched).toBe(true);
    });

    it('should parse . in sequence', () => {
      const validator = parseRegex('a.c');
      expect(validator.match('abc', 0).matched).toBe(true);
      expect(validator.match('axc', 0).matched).toBe(true);
      expect(validator.match('ac', 0).matched).toBe(false);
    });
  });

  describe('complex patterns', () => {
    it('should parse phone number pattern', () => {
      const validator = parseRegex('\\d{3}-\\d{3}-\\d{4}');
      expect(validator.validate('123-456-7890').valid).toBe(true);
      expect(validator.validate('12-456-7890').valid).toBe(false);
    });

    it('should parse email-like pattern', () => {
      const validator = parseRegex('[a-z]+@[a-z]+\\.[a-z]{2,3}');
      expect(validator.validate('test@example.com').valid).toBe(true);
      expect(validator.validate('test@example.c').valid).toBe(false);
    });

    it('should parse hex color pattern', () => {
      const validator = parseRegex('#[0-9a-f]{6}');
      expect(validator.validate('#ff00ff').valid).toBe(true);
      expect(validator.validate('#fff').valid).toBe(false);
    });
  });

  describe('generation', () => {
    it('should generate matching strings for literals', () => {
      const validator = parseRegex('hello');
      expect(validator.generate(rng)).toBe('hello');
    });

    it('should generate matching strings for patterns', () => {
      const validator = parseRegex('\\d{3}');
      for (let i = 0; i < 50; i++) {
        const value = validator.generate(rng);
        expect(value).toMatch(/^\d{3}$/);
      }
    });

    it('should generate valid values for complex patterns', () => {
      const validator = parseRegex('[a-z]+@[a-z]+\\.[a-z]{2,3}');
      for (let i = 0; i < 50; i++) {
        const value = validator.generate(rng);
        expect(validator.validate(value).valid).toBe(true);
      }
    });
  });

  describe('error handling', () => {
    it('should throw on unclosed character class', () => {
      expect(() => parseRegex('[abc')).toThrow();
    });

    it('should throw on unclosed group', () => {
      expect(() => parseRegex('(abc')).toThrow();
    });

    it('should throw on incomplete escape', () => {
      expect(() => parseRegex('\\')).toThrow();
    });
  });
});

