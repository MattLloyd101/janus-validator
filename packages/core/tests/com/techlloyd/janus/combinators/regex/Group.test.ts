import { Group } from '@/com/techlloyd/janus/combinators/regex/Group';
import { Literal } from '@/com/techlloyd/janus/combinators/regex/Literal';
import { Sequence } from '@/com/techlloyd/janus/combinators/regex/Sequence';
import { Alternation } from '@/com/techlloyd/janus/combinators/regex/Alternation';
import { DomainType } from '@/com/techlloyd/janus/Domain';
import { RNG } from '@/com/techlloyd/janus/RNG';

describe('Group', () => {
  describe('capturing group', () => {
    it('should match like inner validator', () => {
      const inner = new Sequence(
        new Literal('a'),
        new Literal('b'),
        new Literal('c')
      );
      const group = Group.capturing(inner);
      
      const result = group.match('abc', 0);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(3);
    });

    it('should have capturing group source', () => {
      const inner = new Literal('x');
      const group = Group.capturing(inner);
      expect(group.domain.source).toBe('(x)');
    });
  });

  describe('non-capturing group', () => {
    it('should match like inner validator', () => {
      const inner = new Sequence(
        new Literal('a'),
        new Literal('b'),
        new Literal('c')
      );
      const group = Group.nonCapturing(inner);
      
      const result = group.match('abc', 0);
      expect(result.matched).toBe(true);
      expect(result.consumed).toBe(3);
    });

    it('should have non-capturing group source', () => {
      const inner = new Literal('x');
      const group = Group.nonCapturing(inner);
      expect(group.domain.source).toBe('(?:x)');
    });
  });

  describe('matching', () => {
    it('should delegate to inner validator', () => {
      const inner = new Alternation(
        new Literal('a'),
        new Literal('b')
      );
      const group = new Group(inner);
      
      expect(group.match('a', 0).matched).toBe(true);
      expect(group.match('b', 0).matched).toBe(true);
      expect(group.match('c', 0).matched).toBe(false);
    });

    it('should match at any position', () => {
      const group = new Group(new Literal('x'));
      expect(group.match('ax', 1).matched).toBe(true);
    });
  });

  describe('validation', () => {
    it('should validate like inner validator', () => {
      const group = new Group(
        new Sequence(new Literal('h'), new Literal('i'))
      );
      expect(group.validate('hi').valid).toBe(true);
      expect(group.validate('h').valid).toBe(false);
      expect(group.validate('hii').valid).toBe(false);
    });

    it('should reject non-strings', () => {
      const group = new Group(new Literal('a'));
      expect(group.validate(123).valid).toBe(false);
    });
  });

  describe('generation', () => {
    it('should generate like inner validator', () => {
      const group = new Group(
        new Sequence(
          new Literal('h'),
          new Literal('e'),
          new Literal('l'),
          new Literal('l'),
          new Literal('o')
        )
      );
      const rng: RNG = { random: () => Math.random() };
      expect(group.generate(rng)).toBe('hello');
    });

    it('should generate from alternation inside group', () => {
      const group = new Group(
        new Alternation(
          new Literal('a'),
          new Literal('b'),
          new Literal('c')
        )
      );
      const rng: RNG = { random: () => Math.random() };

      for (let i = 0; i < 50; i++) {
        const value = group.generate(rng);
        expect(['a', 'b', 'c']).toContain(value);
      }
    });
  });

  describe('domain', () => {
    it('should expose a regex domain', () => {
      const group = new Group(new Literal('x'));
      expect(group.domain.type).toBe(DomainType.REGEX_DOMAIN);
    });

    it('should wrap complex inner in parentheses', () => {
      const inner = new Alternation(
        new Literal('a'),
        new Literal('b')
      );
      const capturing = Group.capturing(inner);
      const nonCapturing = Group.nonCapturing(inner);
      
      expect(capturing.domain.source).toBe('(a|b)');
      expect(nonCapturing.domain.source).toBe('(?:a|b)');
    });
  });

  describe('constructor', () => {
    it('should default to capturing', () => {
      const group = new Group(new Literal('x'));
      expect(group.capturing).toBe(true);
      expect(group.domain.source).toBe('(x)');
    });

    it('should accept capturing parameter', () => {
      const capturing = new Group(new Literal('x'), true);
      const nonCapturing = new Group(new Literal('x'), false);
      
      expect(capturing.capturing).toBe(true);
      expect(nonCapturing.capturing).toBe(false);
    });
  });
});

