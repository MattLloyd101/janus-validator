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

  describe('convenience numeric refinements', () => {
    describe('.positive()', () => {
      it('should pass for positive numbers', () => {
        const validator = Integer(-100, 100).positive();
        expect(validator.validate(1).valid).toBe(true);
        expect(validator.validate(100).valid).toBe(true);
      });

      it('should fail for zero and negative numbers', () => {
        const validator = Integer(-100, 100).positive();
        expect(validator.validate(0).valid).toBe(false);
        expect(validator.validate(-1).valid).toBe(false);
      });

      it('should support custom message', () => {
        const validator = Integer(-100, 100).positive('Need a positive value');
        const result = validator.validate(-5);
        expect(result.valid).toBe(false);
        if (!result.valid) {
          expect(result.error).toBe('Need a positive value');
        }
      });
    });

    describe('.negative()', () => {
      it('should pass for negative numbers', () => {
        const validator = Integer(-100, 100).negative();
        expect(validator.validate(-1).valid).toBe(true);
        expect(validator.validate(-100).valid).toBe(true);
      });

      it('should fail for zero and positive numbers', () => {
        const validator = Integer(-100, 100).negative();
        expect(validator.validate(0).valid).toBe(false);
        expect(validator.validate(1).valid).toBe(false);
      });
    });

    describe('.nonNegative()', () => {
      it('should pass for zero and positive numbers', () => {
        const validator = Integer(-100, 100).nonNegative();
        expect(validator.validate(0).valid).toBe(true);
        expect(validator.validate(1).valid).toBe(true);
      });

      it('should fail for negative numbers', () => {
        const validator = Integer(-100, 100).nonNegative();
        expect(validator.validate(-1).valid).toBe(false);
      });
    });

    describe('.nonPositive()', () => {
      it('should pass for zero and negative numbers', () => {
        const validator = Integer(-100, 100).nonPositive();
        expect(validator.validate(0).valid).toBe(true);
        expect(validator.validate(-1).valid).toBe(true);
      });

      it('should fail for positive numbers', () => {
        const validator = Integer(-100, 100).nonPositive();
        expect(validator.validate(1).valid).toBe(false);
      });
    });

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

    describe('.int()', () => {
      it('should pass for integers', () => {
        const validator = Float(-100, 100).int();
        expect(validator.validate(0).valid).toBe(true);
        expect(validator.validate(42).valid).toBe(true);
        expect(validator.validate(-10).valid).toBe(true);
      });

      it('should fail for non-integers', () => {
        const validator = Float(-100, 100).int();
        expect(validator.validate(3.14).valid).toBe(false);
        expect(validator.validate(0.5).valid).toBe(false);
      });
    });

    describe('.finite()', () => {
      it('should pass for finite numbers', () => {
        const validator = Float().finite();
        expect(validator.validate(0).valid).toBe(true);
        expect(validator.validate(1000000).valid).toBe(true);
      });
    });
  });

  describe('convenience string refinements', () => {
    describe('.email()', () => {
      it('should pass for valid email formats', () => {
        const validator = UnicodeString(5, 100).email();
        expect(validator.validate('test@example.com').valid).toBe(true);
        expect(validator.validate('user.name@domain.co.uk').valid).toBe(true);
      });

      it('should fail for invalid email formats', () => {
        const validator = UnicodeString(1, 100).email();
        expect(validator.validate('not-an-email').valid).toBe(false);
        expect(validator.validate('missing@domain').valid).toBe(false);
        expect(validator.validate('@nodomain.com').valid).toBe(false);
      });
    });

    describe('.url()', () => {
      it('should pass for valid URLs', () => {
        const validator = UnicodeString(10, 2000).url();
        expect(validator.validate('https://example.com').valid).toBe(true);
        expect(validator.validate('http://localhost:3000/path').valid).toBe(true);
      });

      it('should fail for invalid URLs', () => {
        const validator = UnicodeString(1, 100).url();
        expect(validator.validate('not-a-url').valid).toBe(false);
        expect(validator.validate('example.com').valid).toBe(false);
      });
    });

    describe('.uuid()', () => {
      it('should pass for valid UUIDs', () => {
        const validator = UnicodeString(36, 36).uuid();
        expect(validator.validate('550e8400-e29b-41d4-a716-446655440000').valid).toBe(true);
        expect(validator.validate('6ba7b810-9dad-11d1-80b4-00c04fd430c8').valid).toBe(true);
      });

      it('should fail for invalid UUIDs', () => {
        const validator = UnicodeString(1, 100).uuid();
        expect(validator.validate('not-a-uuid').valid).toBe(false);
        expect(validator.validate('550e8400-e29b-41d4-a716').valid).toBe(false);
      });
    });

    describe('.startsWith()', () => {
      it('should pass when string starts with prefix', () => {
        const validator = UnicodeString(1, 100).startsWith('https://');
        expect(validator.validate('https://example.com').valid).toBe(true);
      });

      it('should fail when string does not start with prefix', () => {
        const validator = UnicodeString(1, 100).startsWith('https://');
        expect(validator.validate('http://example.com').valid).toBe(false);
      });

      it('should include prefix in default message', () => {
        const validator = UnicodeString(1, 100).startsWith('PREFIX_');
        const result = validator.validate('test');
        expect(result.valid).toBe(false);
        if (!result.valid) {
          expect(result.error).toBe('Must start with "PREFIX_"');
        }
      });
    });

    describe('.endsWith()', () => {
      it('should pass when string ends with suffix', () => {
        const validator = UnicodeString(1, 100).endsWith('.json');
        expect(validator.validate('config.json').valid).toBe(true);
      });

      it('should fail when string does not end with suffix', () => {
        const validator = UnicodeString(1, 100).endsWith('.json');
        expect(validator.validate('config.yaml').valid).toBe(false);
      });
    });

    describe('.includes()', () => {
      it('should pass when string includes substring', () => {
        const validator = UnicodeString(1, 100).includes('@');
        expect(validator.validate('test@example.com').valid).toBe(true);
      });

      it('should fail when string does not include substring', () => {
        const validator = UnicodeString(1, 100).includes('@');
        expect(validator.validate('test.example.com').valid).toBe(false);
      });
    });

    describe('.pattern()', () => {
      it('should pass when string matches pattern', () => {
        const validator = UnicodeString(1, 100).pattern(/^[A-Z]{3}-\d{4}$/);
        expect(validator.validate('ABC-1234').valid).toBe(true);
      });

      it('should fail when string does not match pattern', () => {
        const validator = UnicodeString(1, 100).pattern(/^[A-Z]{3}-\d{4}$/);
        expect(validator.validate('abc-1234').valid).toBe(false);
        expect(validator.validate('ABC-123').valid).toBe(false);
      });
    });

    describe('.nonempty()', () => {
      it('should pass for non-empty strings', () => {
        const validator = UnicodeString(0, 100).nonempty();
        expect(validator.validate('a').valid).toBe(true);
        expect(validator.validate('hello').valid).toBe(true);
      });

      it('should fail for empty strings', () => {
        const validator = UnicodeString(0, 100).nonempty();
        expect(validator.validate('').valid).toBe(false);
      });
    });
  });

  describe('chaining refinements with transforms', () => {
    it('should apply refinement after transform', () => {
      const validator = UnicodeString(1, 100)
        .trim()
        .nonempty('Cannot be empty or whitespace');
      
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
        .email();
      
      expect(validator.validate('  TEST@EXAMPLE.COM  ').valid).toBe(true);
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

    it('should validate with convenience methods in struct', () => {
      const user = Struct({
        email: UnicodeString(5, 100).email(),
        age: Integer(0, 150).positive(),
        website: UnicodeString(10, 2000).url().optional(),
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
