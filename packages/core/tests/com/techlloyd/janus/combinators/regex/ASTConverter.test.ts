import { parseRegex } from '@/com/techlloyd/janus/combinators/regex/ASTConverter';
import { RNG } from '@/com/techlloyd/janus/RNG';
import { Generator } from '@/com/techlloyd/janus/Generator';

describe('ASTConverter', () => {
  const rng: RNG = { random: () => Math.random() };
  const generator = new Generator(rng);

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

    it('should reject negated character classes as unsupported', () => {
      expect(() => parseRegex('[^abc]')).toThrow('Unsupported regex construct');
    });

    // Non-portable escapes are rejected - use explicit character classes instead
    it('should reject \\d (use [0-9] instead)', () => {
      expect(() => parseRegex('\\d')).toThrow('Unsupported regex escape: \\d');
    });

    it('should reject \\w (use [A-Za-z0-9_] instead)', () => {
      expect(() => parseRegex('\\w')).toThrow('Unsupported regex escape: \\w');
    });

    it('should reject \\s (use [ \\t\\r\\n] instead)', () => {
      expect(() => parseRegex('\\s')).toThrow('Unsupported regex escape: \\s');
    });

    it('should reject \\d inside character class', () => {
      expect(() => parseRegex('[\\d]')).toThrow('Unsupported regex escape: \\d');
    });

    // Explicit character classes work correctly
    it('should parse explicit digit class [0-9]', () => {
      const validator = parseRegex('[0-9]');
      for (let i = 0; i <= 9; i++) {
        expect(validator.match(String(i), 0).matched).toBe(true);
      }
      expect(validator.match('a', 0).matched).toBe(false);
    });

    it('should parse explicit word class [A-Za-z0-9_]', () => {
      const validator = parseRegex('[A-Za-z0-9_]');
      expect(validator.match('a', 0).matched).toBe(true);
      expect(validator.match('Z', 0).matched).toBe(true);
      expect(validator.match('5', 0).matched).toBe(true);
      expect(validator.match('_', 0).matched).toBe(true);
      expect(validator.match('!', 0).matched).toBe(false);
    });

    it('should parse explicit whitespace class [ \\t\\r\\n]', () => {
      const validator = parseRegex('[ \\t\\r\\n]');
      expect(validator.match(' ', 0).matched).toBe(true);
      expect(validator.match('\t', 0).matched).toBe(true);
      expect(validator.match('a', 0).matched).toBe(false);
    });

    it('should parse mixed explicit ranges and literals', () => {
      // [0-9 \t-] should match digits, space, tab, and dash
      const validator = parseRegex('[0-9 \\t\\-]');
      expect(validator.match('5', 0).matched).toBe(true);
      expect(validator.match(' ', 0).matched).toBe(true);
      expect(validator.match('-', 0).matched).toBe(true);
      expect(validator.match('a', 0).matched).toBe(false);
    });

    it('should generate from explicit digit class', () => {
      const validator = parseRegex('[0-9]');
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator.domain);
        expect(value).toMatch(/^[0-9]$/);
      }
    });

    it('should generate from explicit whitespace class', () => {
      const validator = parseRegex('[ \\t\\r\\n]');
      for (let i = 0; i < 20; i++) {
        const value = generator.generate(validator.domain);
        expect(value).toMatch(/^[ \t\r\n]$/);
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

    it('should reject \\b anchor (not portable)', () => {
      // Word boundary is not portable across regex engines
      expect(() => parseRegex('\\b')).toThrow('Unsupported regex escape: \\b');
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
    it('should parse phone number pattern (using explicit [0-9])', () => {
      const validator = parseRegex('[0-9]{3}-[0-9]{3}-[0-9]{4}');
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
      expect(generator.generate(validator.domain)).toBe('hello');
    });

    it('should generate matching strings for digit patterns (using explicit [0-9])', () => {
      const validator = parseRegex('[0-9]{3}');
      for (let i = 0; i < 50; i++) {
        const value = generator.generate(validator.domain);
        expect(value).toMatch(/^[0-9]{3}$/);
      }
    });

    it('should generate valid values for complex patterns', () => {
      const validator = parseRegex('[a-z]+@[a-z]+\\.[a-z]{2,3}');
      for (let i = 0; i < 50; i++) {
        const value = generator.generate(validator.domain);
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

