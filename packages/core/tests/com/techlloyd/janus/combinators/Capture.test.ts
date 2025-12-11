import { Capture, Ref, ValidationContext, createCaptureGroup } from '@/com/techlloyd/janus/combinators/Capture';
import { Struct } from '@/com/techlloyd/janus/combinators/Struct';
import { Integer } from '@/com/techlloyd/janus/combinators/Integer';
import { UnicodeString } from '@/com/techlloyd/janus/combinators/UnicodeString';
import { DomainType } from '@/com/techlloyd/janus/index';

describe('Capture and Ref', () => {
  describe('ValidationContext', () => {
    it('should store and retrieve values', () => {
      const ctx = new ValidationContext();
      ctx.set('test', 42);
      expect(ctx.get('test')).toBe(42);
    });

    it('should check if value exists', () => {
      const ctx = new ValidationContext();
      expect(ctx.has('missing')).toBe(false);
      ctx.set('exists', 'value');
      expect(ctx.has('exists')).toBe(true);
    });

    it('should clear all values', () => {
      const ctx = new ValidationContext();
      ctx.set('a', 1);
      ctx.set('b', 2);
      ctx.clear();
      expect(ctx.has('a')).toBe(false);
      expect(ctx.has('b')).toBe(false);
    });

    it('should return all captured values', () => {
      const ctx = new ValidationContext();
      ctx.set('name', 'Alice');
      ctx.set('age', 30);
      expect(ctx.all()).toEqual({ name: 'Alice', age: 30 });
    });
  });

  describe('Capture', () => {
    it('should validate using inner validator', () => {
      const ctx = new ValidationContext();
      const capture = new Capture(ctx, 'num', Integer(0, 100));

      expect(capture.validate(50).valid).toBe(true);
      expect(capture.validate(150).valid).toBe(false);
      expect(capture.validate('not a number').valid).toBe(false);
    });

    it('should store captured value in context on success', () => {
      const ctx = new ValidationContext();
      const capture = new Capture(ctx, 'myValue', Integer(0, 100));

      capture.validate(42);
      expect(ctx.get('myValue')).toBe(42);
    });

    it('should not store value in context on failure', () => {
      const ctx = new ValidationContext();
      const capture = new Capture(ctx, 'myValue', Integer(0, 100));

      capture.validate(150); // Invalid
      expect(ctx.has('myValue')).toBe(false);
    });

    it('should expose capture domain', () => {
      const ctx = new ValidationContext();
      const capture = new Capture(ctx, 'test', UnicodeString());

      expect(capture.domain.type).toBe(DomainType.CAPTURE_DOMAIN);
      expect(capture.domain.name).toBe('test');
    });
  });

  describe('Ref', () => {
    it('should validate against captured value', () => {
      const ctx = new ValidationContext();
      ctx.set('password', 'secret123');
      
      const ref = new Ref<string>(ctx, 'password');

      expect(ref.validate('secret123').valid).toBe(true);
      expect(ref.validate('different').valid).toBe(false);
    });

    it('should fail if reference not captured yet', () => {
      const ctx = new ValidationContext();
      const ref = new Ref<string>(ctx, 'missing');

      const result = ref.validate('anything');
      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('not been captured');
      }
    });

    it('should support custom comparator', () => {
      const ctx = new ValidationContext();
      ctx.set('obj', { id: 1, name: 'test' });
      
      // Deep equality comparator
      const ref = new Ref<object>(ctx, 'obj', (a, b) => 
        JSON.stringify(a) === JSON.stringify(b)
      );

      expect(ref.validate({ id: 1, name: 'test' }).valid).toBe(true);
      expect(ref.validate({ id: 2, name: 'test' }).valid).toBe(false);
    });

    it('should expose ref domain', () => {
      const ctx = new ValidationContext();
      const ref = new Ref<string>(ctx, 'test');

      expect(ref.domain.type).toBe(DomainType.REF_DOMAIN);
      expect(ref.domain.name).toBe('test');
    });
  });

  describe('createCaptureGroup', () => {
    it('should create linked capture and ref functions', () => {
      const { capture, ref } = createCaptureGroup();
      
      const captureValidator = capture('test', UnicodeString());
      const refValidator = ref<string>('test');

      // Capture a value
      captureValidator.validate('hello');
      
      // Ref should match
      expect(refValidator.validate('hello').valid).toBe(true);
      expect(refValidator.validate('world').valid).toBe(false);
    });

    it('should share context between capture and ref', () => {
      const { capture, ref, context } = createCaptureGroup();
      
      capture('value', Integer()).validate(42);
      
      expect(context.get('value')).toBe(42);
      expect(ref<number>('value').validate(42).valid).toBe(true);
    });
  });

  describe('password confirmation use case', () => {
    it('should validate matching passwords', () => {
      const { capture, ref, context } = createCaptureGroup();
      
      const validator = Struct({
        password: capture('pwd', UnicodeString(8, 50)),
        confirmPassword: ref<string>('pwd'),
      });

      // Valid - passwords match
      const validResult = validator.validate({
        password: 'secret123',
        confirmPassword: 'secret123',
      });
      expect(validResult.valid).toBe(true);

      // Clear context for next validation
      context.clear();

      // Invalid - passwords don't match
      const invalidResult = validator.validate({
        password: 'secret123',
        confirmPassword: 'different',
      });
      expect(invalidResult.valid).toBe(false);
    });

    it('should validate email confirmation', () => {
      const { capture, ref, context } = createCaptureGroup();
      
      const validator = Struct({
        email: capture('email', UnicodeString(5, 100)),
        confirmEmail: ref<string>('email'),
      });

      expect(validator.validate({
        email: 'user@example.com',
        confirmEmail: 'user@example.com',
      }).valid).toBe(true);

      context.clear();

      expect(validator.validate({
        email: 'user@example.com',
        confirmEmail: 'other@example.com',
      }).valid).toBe(false);
    });
  });

  describe('nested capture use case', () => {
    it('should work with nested objects', () => {
      const { capture, ref, context } = createCaptureGroup();
      
      const validator = Struct({
        user: Struct({
          id: capture('userId', Integer(1, 1000)),
        }),
        audit: Struct({
          createdBy: ref<number>('userId'),
        }),
      });

      expect(validator.validate({
        user: { id: 42 },
        audit: { createdBy: 42 },
      }).valid).toBe(true);

      context.clear();

      expect(validator.validate({
        user: { id: 42 },
        audit: { createdBy: 99 },
      }).valid).toBe(false);
    });
  });

  describe('multiple captures', () => {
    it('should support multiple independent captures', () => {
      const { capture, ref, context } = createCaptureGroup();
      
      const validator = Struct({
        fieldA: capture('a', UnicodeString()),
        fieldB: capture('b', Integer()),
        refA: ref<string>('a'),
        refB: ref<number>('b'),
      });

      expect(validator.validate({
        fieldA: 'hello',
        fieldB: 42,
        refA: 'hello',
        refB: 42,
      }).valid).toBe(true);

      context.clear();

      // refA doesn't match
      expect(validator.validate({
        fieldA: 'hello',
        fieldB: 42,
        refA: 'world',
        refB: 42,
      }).valid).toBe(false);
    });
  });

  describe('context reuse', () => {
    it('should require clearing context between validations', () => {
      const { capture, ref, context } = createCaptureGroup();
      
      const validator = Struct({
        value: capture('val', Integer()),
        confirm: ref<number>('val'),
      });

      // First validation
      validator.validate({ value: 10, confirm: 10 });
      
      // Without clearing, the old captured value persists
      // This could cause unexpected behavior
      const result = validator.validate({ value: 20, confirm: 20 });
      expect(result.valid).toBe(true);

      // Verify the new value was captured
      expect(context.get('val')).toBe(20);
    });
  });
});

