import { UnicodeString } from '@/com/techlloyd/janus/combinators/UnicodeString';
import { Integer } from '@/com/techlloyd/janus/combinators/Integer';
import { Boolean } from '@/com/techlloyd/janus/combinators/Boolean';
import { Struct } from '@/com/techlloyd/janus/combinators/Struct';
import { Sequence } from '@/com/techlloyd/janus/combinators/Sequence';
import { Quantifier } from '@/com/techlloyd/janus/combinators/Quantifier';
import {
  message,
  code,
  describe as describeValidator,
  MessageValidator,
  CodeValidator,
  DescribeValidator,
} from '@/com/techlloyd/janus/combinators/modifiers';
import {
  formatPath,
  prependPath,
  flattenErrors,
  formatErrors,
  errorsToJson,
  getFirstError,
  getErrorAtPath,
  getErrorsByPath,
  ValidationResult,
} from '@/com/techlloyd/janus/index';

describe('Enhanced Error Messages', () => {
  describe('formatPath', () => {
    it('should format empty path', () => {
      expect(formatPath([])).toBe('');
    });

    it('should format single key', () => {
      expect(formatPath(['name'])).toBe('name');
    });

    it('should format nested keys', () => {
      expect(formatPath(['user', 'profile', 'name'])).toBe('user.profile.name');
    });

    it('should format array indices', () => {
      expect(formatPath(['items', 0, 'name'])).toBe('items[0].name');
    });

    it('should format complex paths', () => {
      expect(formatPath(['users', 0, 'addresses', 1, 'zip'])).toBe('users[0].addresses[1].zip');
    });
  });

  describe('prependPath', () => {
    it('should return valid results unchanged', () => {
      const result: ValidationResult<string> = { valid: true, value: 'test' };
      expect(prependPath(result, 'key')).toBe(result);
    });

    it('should prepend string key to empty path', () => {
      const result: ValidationResult<string> = { valid: false, error: 'Invalid' };
      const updated = prependPath(result, 'name');
      expect(updated.valid).toBe(false);
      if (!updated.valid) {
        expect(updated.path).toEqual(['name']);
        expect(updated.pathString).toBe('name');
      }
    });

    it('should prepend string key to existing path', () => {
      const result: ValidationResult<string> = { valid: false, error: 'Invalid', path: ['email'] };
      const updated = prependPath(result, 'user');
      expect(updated.valid).toBe(false);
      if (!updated.valid) {
        expect(updated.path).toEqual(['user', 'email']);
        expect(updated.pathString).toBe('user.email');
      }
    });

    it('should prepend number index', () => {
      const result: ValidationResult<string> = { valid: false, error: 'Invalid', path: ['name'] };
      const updated = prependPath(result, 0);
      expect(updated.valid).toBe(false);
      if (!updated.valid) {
        expect(updated.path).toEqual([0, 'name']);
        expect(updated.pathString).toBe('[0].name');
      }
    });
  });

  describe('MessageValidator', () => {
    describe('standalone function', () => {
      it('should override error message with static string', () => {
        const validator = message(Integer(0, 100), 'Please enter a valid number');
        
        const result = validator.validate(150);
        expect(result.valid).toBe(false);
        if (!result.valid) {
          expect(result.error).toBe('Please enter a valid number');
        }
      });

      it('should pass valid values through', () => {
        const validator = message(Integer(0, 100), 'Custom error');
        
        const result = validator.validate(50);
        expect(result).toEqual({ valid: true, value: 50 });
      });

      it('should support dynamic message function', () => {
        const validator = message(
          Integer(0, 100),
          (err, val) => `Got ${val}: ${err}`
        );
        
        const result = validator.validate(150);
        expect(result.valid).toBe(false);
        if (!result.valid) {
          expect(result.error).toMatch(/Got 150:/);
        }
      });
    });

    describe('fluent method', () => {
      it('should work with fluent API', () => {
        const validator = Integer(0, 100).message('Invalid age');
        
        const result = validator.validate(200);
        expect(result.valid).toBe(false);
        if (!result.valid) {
          expect(result.error).toBe('Invalid age');
        }
      });

      it('should chain with other modifiers', () => {
        const validator = UnicodeString(1, 50)
          .refine(s => s.includes('@'), 'Must contain @')
          .message('Please enter a valid email');
        
        const result = validator.validate('invalid');
        expect(result.valid).toBe(false);
        if (!result.valid) {
          expect(result.error).toBe('Please enter a valid email');
        }
      });
    });
  });

  describe('CodeValidator', () => {
    describe('standalone function', () => {
      it('should add error code', () => {
        const validator = code(Integer(0, 100), 'INVALID_NUMBER');
        
        const result = validator.validate(150);
        expect(result.valid).toBe(false);
        if (!result.valid) {
          expect(result.code).toBe('INVALID_NUMBER');
        }
      });

      it('should pass valid values through', () => {
        const validator = code(Integer(0, 100), 'ERROR');
        
        const result = validator.validate(50);
        expect(result).toEqual({ valid: true, value: 50 });
      });
    });

    describe('fluent method', () => {
      it('should work with fluent API', () => {
        const validator = UnicodeString(5, 100)
          .refine(s => s.includes('@'))
          .code('INVALID_EMAIL');
        
        const result = validator.validate('test');
        expect(result.valid).toBe(false);
        if (!result.valid) {
          expect(result.code).toBe('INVALID_EMAIL');
        }
      });
    });
  });

  describe('DescribeValidator', () => {
    describe('standalone function', () => {
      it('should add description to meta', () => {
        const validator = describeValidator(Integer(0, 150), 'User age in years');
        
        const result = validator.validate(200);
        expect(result.valid).toBe(false);
        if (!result.valid) {
          expect(result.meta?.description).toBe('User age in years');
        }
      });

      it('should expose description property', () => {
        const validator = describeValidator(Integer(0, 150), 'User age in years');
        
        expect(validator.description).toBe('User age in years');
      });

      it('should pass valid values through', () => {
        const validator = describeValidator(Integer(0, 150), 'Age');
        
        const result = validator.validate(25);
        expect(result).toEqual({ valid: true, value: 25 });
      });
    });

    describe('fluent method', () => {
      it('should work with fluent API', () => {
        const validator = UnicodeString(5, 100).describe('User email address');
        
        expect(validator.description).toBe('User email address');
      });
    });
  });

  describe('Path tracking in composite validators', () => {
    describe('Struct', () => {
      it('should include path in nested errors', () => {
        const validator = Struct({
          name: UnicodeString(1, 50),
          age: Integer(0, 150),
        });
        
        const result = validator.validate({ name: 'Alice', age: 200 });
        expect(result.valid).toBe(false);
        if (!result.valid && result.results && !Array.isArray(result.results)) {
          const ageResult = result.results['age'];
          expect(ageResult.valid).toBe(false);
          if (!ageResult.valid) {
            expect(ageResult.path).toEqual(['age']);
            expect(ageResult.pathString).toBe('age');
          }
        }
      });

      it('should include path for missing required fields', () => {
        const validator = Struct({
          name: UnicodeString(1, 50),
          age: Integer(0, 150),
        });
        
        const result = validator.validate({ name: 'Alice' });
        expect(result.valid).toBe(false);
        if (!result.valid && result.results && !Array.isArray(result.results)) {
          const ageResult = result.results['age'];
          expect(ageResult.valid).toBe(false);
          if (!ageResult.valid) {
            expect(ageResult.path).toEqual(['age']);
          }
        }
      });

      it('should include path for strict mode extra fields', () => {
        const validator = Struct({ name: UnicodeString(1, 50) }, true);
        
        const result = validator.validate({ name: 'Alice', extra: 123 });
        expect(result.valid).toBe(false);
        if (!result.valid && result.results && !Array.isArray(result.results)) {
          const extraResult = result.results['extra'];
          expect(extraResult.valid).toBe(false);
          if (!extraResult.valid) {
            expect(extraResult.path).toEqual(['extra']);
          }
        }
      });

      it('should handle nested structs', () => {
        const validator = Struct({
          user: Struct({
            profile: Struct({
              email: UnicodeString(5, 100),
            }),
          }),
        });
        
        const result = validator.validate({
          user: { profile: { email: '' } },
        });
        expect(result.valid).toBe(false);
        
        // Flatten to check full path
        const errors = flattenErrors(result);
        expect(errors[0].path).toBe('user.profile.email');
      });
    });

    describe('Sequence', () => {
      it('should include index in path', () => {
        const validator = Sequence.of(
          Integer(0, 100),
          UnicodeString(1, 50),
          Boolean()
        );
        
        const result = validator.validate([50, '', true]);
        expect(result.valid).toBe(false);
        if (!result.valid && Array.isArray(result.results)) {
          const secondResult = result.results[1];
          expect(secondResult.valid).toBe(false);
          if (!secondResult.valid) {
            expect(secondResult.path).toEqual([1]);
            expect(secondResult.pathString).toBe('[1]');
          }
        }
      });
    });

    describe('Quantifier', () => {
      it('should include index in path for invalid elements', () => {
        const validator = Quantifier.oneOrMore(Integer(0, 100));
        
        const result = validator.validate([50, 150, 25]);
        expect(result.valid).toBe(false);
        if (!result.valid && Array.isArray(result.results)) {
          const secondResult = result.results[1];
          expect(secondResult.valid).toBe(false);
          if (!secondResult.valid) {
            expect(secondResult.path).toEqual([1]);
            expect(secondResult.pathString).toBe('[1]');
          }
        }
      });
    });
  });

  describe('Error formatting utilities', () => {
    const User = Struct({
      profile: Struct({
        name: UnicodeString(1, 50).message('Name is required'),
        email: UnicodeString(5, 100)
          .refine(s => s.includes('@'), 'Invalid email')
          .code('INVALID_EMAIL'),
      }),
      age: Integer(0, 150),
    });

    describe('flattenErrors', () => {
      it('should return empty array for valid results', () => {
        const result = User.validate({
          profile: { name: 'Alice', email: 'alice@example.com' },
          age: 30,
        });
        expect(flattenErrors(result)).toEqual([]);
      });

      it('should flatten nested errors', () => {
        const result = User.validate({
          profile: { name: '', email: 'invalid' },
          age: 200,
        });
        
        const errors = flattenErrors(result);
        expect(errors.length).toBeGreaterThan(0);
        expect(errors.some(e => e.path.includes('profile.name'))).toBe(true);
        expect(errors.some(e => e.path.includes('profile.email'))).toBe(true);
      });

      it('should include error codes', () => {
        const result = User.validate({
          profile: { name: 'Alice', email: 'invalid' },
          age: 30,
        });
        
        const errors = flattenErrors(result);
        const emailError = errors.find(e => e.path === 'profile.email');
        expect(emailError?.code).toBe('INVALID_EMAIL');
      });
    });

    describe('formatErrors', () => {
      it('should return empty string for valid results', () => {
        const result = User.validate({
          profile: { name: 'Alice', email: 'alice@example.com' },
          age: 30,
        });
        expect(formatErrors(result)).toBe('');
      });

      it('should format errors with paths', () => {
        const result = User.validate({
          profile: { name: '', email: 'alice@example.com' },
          age: 30,
        });
        
        const formatted = formatErrors(result);
        expect(formatted).toContain('profile.name');
        expect(formatted).toContain('Name is required');
      });
    });

    describe('errorsToJson', () => {
      it('should return valid JSON for valid results', () => {
        const result = User.validate({
          profile: { name: 'Alice', email: 'alice@example.com' },
          age: 30,
        });
        expect(errorsToJson(result)).toEqual({ valid: true, errors: [] });
      });

      it('should return structured JSON for invalid results', () => {
        const result = User.validate({
          profile: { name: 'Alice', email: 'invalid' },
          age: 30,
        });
        
        const json = errorsToJson(result);
        expect(json.valid).toBe(false);
        expect(json.errors.length).toBeGreaterThan(0);
        expect(json.errors[0]).toHaveProperty('path');
        expect(json.errors[0]).toHaveProperty('message');
        expect(json.errors[0]).toHaveProperty('code');
      });
    });

    describe('getFirstError', () => {
      it('should return null for valid results', () => {
        const result = User.validate({
          profile: { name: 'Alice', email: 'alice@example.com' },
          age: 30,
        });
        expect(getFirstError(result)).toBeNull();
      });

      it('should return first error for invalid results', () => {
        const result = User.validate({
          profile: { name: '', email: 'invalid' },
          age: 200,
        });
        
        const first = getFirstError(result);
        expect(first).not.toBeNull();
        expect(first?.message).toBeTruthy();
      });
    });

    describe('getErrorAtPath', () => {
      it('should return null for valid results', () => {
        const result = User.validate({
          profile: { name: 'Alice', email: 'alice@example.com' },
          age: 30,
        });
        expect(getErrorAtPath(result, 'profile.name')).toBeNull();
      });

      it('should return error at specific path', () => {
        const result = User.validate({
          profile: { name: '', email: 'alice@example.com' },
          age: 30,
        });
        
        const error = getErrorAtPath(result, 'profile.name');
        expect(error).not.toBeNull();
        expect(error?.message).toBe('Name is required');
      });

      it('should return null for non-existent path', () => {
        const result = User.validate({
          profile: { name: '', email: 'alice@example.com' },
          age: 30,
        });
        
        expect(getErrorAtPath(result, 'profile.phone')).toBeNull();
      });
    });

    describe('getErrorsByPath', () => {
      it('should return empty object for valid results', () => {
        const result = User.validate({
          profile: { name: 'Alice', email: 'alice@example.com' },
          age: 30,
        });
        expect(getErrorsByPath(result)).toEqual({});
      });

      it('should group errors by path', () => {
        const result = User.validate({
          profile: { name: '', email: 'invalid' },
          age: 200,
        });
        
        const byPath = getErrorsByPath(result);
        expect(byPath['profile.name']).toBeDefined();
        expect(byPath['profile.email']).toBeDefined();
        expect(byPath['age']).toBeDefined();
      });
    });
  });

  describe('Combined usage', () => {
    it('should work with all modifiers together', () => {
      const email = UnicodeString(5, 100)
        .refine(s => s.includes('@'), 'Must contain @')
        .message('Please enter a valid email address')
        .code('INVALID_EMAIL')
        .describe('User email for account recovery');
      
      expect(email.description).toBe('User email for account recovery');
      
      const result = email.validate('bad');
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toBe('Please enter a valid email address');
        expect(result.code).toBe('INVALID_EMAIL');
        expect(result.meta?.description).toBe('User email for account recovery');
      }
    });

    it('should preserve inner validator domain', () => {
      const inner = Integer(0, 100);
      const wrapped = inner.message('Error').code('CODE').describe('Desc');
      
      expect(wrapped.domain).toBe(inner.domain);
    });
  });
});
