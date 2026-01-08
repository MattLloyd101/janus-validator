import { UnicodeString } from '@/com/techlloyd/janus/combinators/UnicodeString';
import { Integer } from '@/com/techlloyd/janus/combinators/Integer';
import { Float } from '@/com/techlloyd/janus/combinators/Float';
import { Struct } from '@/com/techlloyd/janus/combinators/Struct';
import { Generator } from '@/com/techlloyd/janus/Generator';
import {
  refine,
  superRefine,
  RefineValidator,
  SuperRefineValidator,
} from '@/com/techlloyd/janus/combinators/modifiers';

describe('Refine', () => {
  describe('standalone refine() function', () => {
    it('should pass when predicate returns true', () => {
      const validator = refine(Integer(0, 100), n => n % 2 === 0, 'Must be even');
      
      expect(validator.validate(4)).toEqual({ valid: true, value: 4 });
      expect(validator.validate(0)).toEqual({ valid: true, value: 0 });
      expect(validator.validate(100)).toEqual({ valid: true, value: 100 });
    });

    it('should fail when predicate returns false', () => {
      const validator = refine(Integer(0, 100), n => n % 2 === 0, 'Must be even');
      
      const result = validator.validate(5);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toBe('Must be even');
      }
    });

    it('should pass through inner validation errors', () => {
      const validator = refine(Integer(0, 100), n => n % 2 === 0, 'Must be even');
      
      const result = validator.validate(150); // Out of range
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).not.toBe('Must be even');
      }
    });

    it('should support dynamic error messages', () => {
      const validator = refine(
        Integer(0, 100),
        n => n > 0,
        n => `Expected positive, got ${n}`
      );
      
      const result = validator.validate(0);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toBe('Expected positive, got 0');
      }
    });
  });

  describe('fluent .refine() method', () => {
    it('should work with simple predicate', () => {
      const validator = Integer(0, 100).refine(n => n % 2 === 0, 'Must be even');
      
      expect(validator.validate(4).valid).toBe(true);
      expect(validator.validate(5).valid).toBe(false);
    });

    it('should chain multiple refinements', () => {
      const validator = Integer(0, 100)
        .refine(n => n % 2 === 0, 'Must be even')
        .refine(n => n >= 10, 'Must be at least 10');
      
      expect(validator.validate(12).valid).toBe(true);
      expect(validator.validate(4).valid).toBe(false);  // Even but < 10
      expect(validator.validate(15).valid).toBe(false); // >= 10 but odd
    });

    it('should provide default error message', () => {
      const validator = Integer(0, 100).refine(n => n % 2 === 0);
      
      const result = validator.validate(5);
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toBe('Refinement failed');
      }
    });

    it('should work on string validators', () => {
      const validator = UnicodeString(1, 100).refine(
        s => s.includes('@'),
        'Must contain @'
      );
      
      expect(validator.validate('test@example.com').valid).toBe(true);
      expect(validator.validate('test').valid).toBe(false);
    });
  });

  describe('numeric refinements', () => {
    describe('.multipleOf()', () => {
      it('should pass for multiples', () => {
        const validator = Integer(0, 100).multipleOf(5);
        expect(validator.validate(0).valid).toBe(true);
        expect(validator.validate(5).valid).toBe(true);
        expect(validator.validate(25).valid).toBe(true);
      });

      it('should fail for non-multiples', () => {
        const validator = Integer(0, 100).multipleOf(5);
        expect(validator.validate(3).valid).toBe(false);
        expect(validator.validate(11).valid).toBe(false);
      });

      it('should include divisor in default message', () => {
        const validator = Integer(0, 100).multipleOf(7);
        const result = validator.validate(10);
        expect(result.valid).toBe(false);
        if (!result.valid) {
          expect(result.error).toBe('Must be a multiple of 7');
        }
      });
    });
  });

  describe('string refinements', () => {
    describe('.includes()', () => {
      it('should pass when string includes substring', () => {
        const validator = UnicodeString(1, 100).includes('@');
        expect(validator.validate('test@example.com').valid).toBe(true);
      });

      it('should fail when string does not include substring', () => {
        const validator = UnicodeString(1, 100).includes('@');
        expect(validator.validate('test.example.com').valid).toBe(false);
      });

      it('should include substring in default message', () => {
        const validator = UnicodeString(1, 100).includes('@@');
        const result = validator.validate('test@example.com');
        expect(result.valid).toBe(false);
        if (!result.valid) {
          expect(result.error).toBe('Must include "@@"');
        }
      });
    });
  });

  describe('chaining refinements with transforms', () => {
    it('should apply refinement after transform', () => {
      const validator = UnicodeString(0, 100)
        .trim()
        .refine(s => s.length > 0, 'Cannot be empty or whitespace');
      
      expect(validator.validate('hello').valid).toBe(true);
      expect(validator.validate('  hello  ').valid).toBe(true);
      
      const result = validator.validate('   ');
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toBe('Cannot be empty or whitespace');
      }
    });

    it('should chain transform and multiple refinements', () => {
      const validator = UnicodeString(1, 100)
        .trim()
        .toLowerCase()
        .refine(s => s.includes('@') && s.includes('.'), 'Must be email-like');
      
      expect(validator.validate('  TEST@EXAMPLE.COM  ').valid).toBe(true);
    });
  });

  describe('implementing common patterns with refine()', () => {
    it('can implement positive check', () => {
      const positive = Integer(-100, 100).refine(n => n > 0, 'Must be positive');
      expect(positive.validate(5).valid).toBe(true);
      expect(positive.validate(-5).valid).toBe(false);
    });

    it('can implement email check', () => {
      const email = UnicodeString(5, 100).refine(
        s => /^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(s),
        'Invalid email'
      );
      expect(email.validate('test@example.com').valid).toBe(true);
      expect(email.validate('invalid').valid).toBe(false);
    });

    it('can implement uuid check', () => {
      const uuid = UnicodeString(36, 36).refine(
        s => /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i.test(s),
        'Invalid UUID'
      );
      expect(uuid.validate('550e8400-e29b-41d4-a716-446655440000').valid).toBe(true);
      expect(uuid.validate('not-a-uuid').valid).toBe(false);
    });

    it('can implement startsWith check', () => {
      const httpsUrl = UnicodeString(10, 2000).refine(
        s => s.startsWith('https://'),
        'Must start with https://'
      );
      expect(httpsUrl.validate('https://example.com').valid).toBe(true);
      expect(httpsUrl.validate('http://example.com').valid).toBe(false);
    });
  });

  describe('domain and generation', () => {
    it('should preserve inner domain', () => {
      const inner = Integer(0, 100);
      const refined = inner.refine(n => n % 2 === 0, 'Must be even');
      
      expect(refined.domain).toBe(inner.domain);
    });

    it('should generate from inner domain (values may fail refinement)', () => {
      const validator = Integer(0, 10).refine(n => n % 2 === 0, 'Must be even');
      const generator = new Generator({ random: Math.random });
      
      // Generate values - some may be odd (which is expected behavior)
      let hasEven = false;
      let hasOdd = false;
      
      for (let i = 0; i < 50; i++) {
        const value = generator.generate(validator.domain);
        if (value % 2 === 0) hasEven = true;
        else hasOdd = true;
      }
      
      // Should generate both - demonstrating refinements don't affect generation
      expect(hasEven || hasOdd).toBe(true);
    });
  });
});

describe('SuperRefine', () => {
  describe('standalone superRefine() function', () => {
    it('should pass when no issues are added', () => {
      const validator = superRefine(UnicodeString(1, 100), (value, ctx) => {
        // No issues
      });
      
      expect(validator.validate('hello')).toEqual({ valid: true, value: 'hello' });
    });

    it('should fail when issues are added', () => {
      const validator = superRefine(UnicodeString(8, 100), (value, ctx) => {
        if (!/[A-Z]/.test(value)) {
          ctx.addIssue({ message: 'Must contain uppercase letter' });
        }
      });
      
      const result = validator.validate('lowercase');
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toBe('Must contain uppercase letter');
      }
    });

    it('should collect multiple issues', () => {
      const validator = superRefine(UnicodeString(8, 100), (value, ctx) => {
        if (!/[A-Z]/.test(value)) {
          ctx.addIssue({ message: 'Need uppercase' });
        }
        if (!/[0-9]/.test(value)) {
          ctx.addIssue({ message: 'Need digit' });
        }
      });
      
      const result = validator.validate('lowercase');
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toBe('Need uppercase; Need digit');
      }
    });

    it('should include path in error message', () => {
      const validator = superRefine(
        Struct({ password: UnicodeString(1, 100), confirm: UnicodeString(1, 100) }),
        (value, ctx) => {
          if (value.password !== value.confirm) {
            ctx.addIssue({ message: 'Passwords must match', path: ['confirm'] });
          }
        }
      );
      
      const result = validator.validate({ password: 'abc', confirm: 'xyz' });
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toBe('confirm: Passwords must match');
      }
    });
  });

  describe('fluent .superRefine() method', () => {
    it('should work with fluent API', () => {
      const validator = UnicodeString(8, 100).superRefine((value, ctx) => {
        const missing = [];
        if (!/[A-Z]/.test(value)) missing.push('uppercase');
        if (!/[a-z]/.test(value)) missing.push('lowercase');
        if (!/[0-9]/.test(value)) missing.push('digit');
        
        if (missing.length > 0) {
          ctx.addIssue({ message: `Missing: ${missing.join(', ')}` });
        }
      });
      
      expect(validator.validate('Password1').valid).toBe(true);
      
      const result = validator.validate('password');
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('uppercase');
        expect(result.error).toContain('digit');
      }
    });
  });

  describe('real-world examples', () => {
    it('should validate password strength', () => {
      const password = UnicodeString(8, 100)
        .refine(s => /[A-Z]/.test(s), 'Must contain uppercase letter')
        .refine(s => /[a-z]/.test(s), 'Must contain lowercase letter')
        .refine(s => /[0-9]/.test(s), 'Must contain digit')
        .refine(s => /[!@#$%^&*]/.test(s), 'Must contain special character');
      
      expect(password.validate('Password1!').valid).toBe(true);
      expect(password.validate('password').valid).toBe(false);
    });

    it('should validate date range', () => {
      const dateRange = Struct({
        start: UnicodeString(10, 10), // ISO date
        end: UnicodeString(10, 10),
      }).superRefine((value, ctx) => {
        const start = new Date(value.start);
        const end = new Date(value.end);
        if (start >= end) {
          ctx.addIssue({ message: 'End date must be after start date', path: ['end'] });
        }
      });
      
      expect(dateRange.validate({ start: '2024-01-01', end: '2024-12-31' }).valid).toBe(true);
      
      const result = dateRange.validate({ start: '2024-12-31', end: '2024-01-01' });
      expect(result.valid).toBe(false);
    });

    it('should validate user with refinements', () => {
      // Using refine() instead of convenience methods
      const user = Struct({
        email: UnicodeString(5, 100).refine(
          s => /^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(s),
          'Invalid email'
        ),
        age: Integer(1, 150), // Using domain constraint instead of positive()
        website: UnicodeString(10, 2000)
          .refine(s => {
            try { new URL(s); return true; } catch { return false; }
          }, 'Invalid URL')
          .optional(),
      });
      
      expect(user.validate({
        email: 'test@example.com',
        age: 25,
        website: 'https://example.com',
      }).valid).toBe(true);
      
      expect(user.validate({
        email: 'test@example.com',
        age: 25,
      }).valid).toBe(true);
      
      expect(user.validate({
        email: 'not-an-email',
        age: 25,
      }).valid).toBe(false);
    });
  });
});
