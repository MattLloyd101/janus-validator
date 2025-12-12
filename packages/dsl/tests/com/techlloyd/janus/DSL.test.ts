import {
  B, U, S, I, N, L, R, O, C, Bytes, Or, Seq, Enum,
  Null, Undefined, Inf, NInf, NaN,
  zeroOrMore, oneOrMore, optional, exactly, atLeast, between, digits, hex,
} from '@/com/techlloyd/janus/index';

describe('DSL', () => {
  describe('primitive validators', () => {
    describe('B (Boolean)', () => {
      it('should validate booleans', () => {
        const validator = B();
        expect(validator.validate(true).valid).toBe(true);
        expect(validator.validate(false).valid).toBe(true);
        expect(validator.validate('true').valid).toBe(false);
      });

      it('should include example on error', () => {
        const validator = B();
        const result = validator.validate('not boolean');
        expect(result.valid).toBe(false);
        if (!result.valid) {
          expect(result.example).toBeDefined();
          expect(typeof result.example).toBe('boolean');
        }
      });
    });

    describe('U (UnicodeString)', () => {
      it('should validate strings', () => {
        const validator = U();
        expect(validator.validate('hello').valid).toBe(true);
        expect(validator.validate(123).valid).toBe(false);
      });

      it('should respect length constraints', () => {
        const validator = U(2, 5);
        expect(validator.validate('hi').valid).toBe(true);
        expect(validator.validate('hello').valid).toBe(true);
        expect(validator.validate('x').valid).toBe(false);
        expect(validator.validate('toolong').valid).toBe(false);
      });
    });

    describe('S (String - Compound)', () => {
      it('should validate compound strings with literals', () => {
        const validator = S('hello');
        expect(validator.validate('hello').valid).toBe(true);
        expect(validator.validate('world').valid).toBe(false);
      });

      it('should validate compound strings with parts', () => {
        const validator = S('ID-', digits(4));
        expect(validator.validate('ID-1234').valid).toBe(true);
        expect(validator.validate('ID-123').valid).toBe(false);
        expect(validator.validate('XX-1234').valid).toBe(false);
      });

      it('should validate UUID format', () => {
        const uuid = S(hex(8), '-', hex(4), '-', hex(4), '-', hex(4), '-', hex(12));
        expect(uuid.validate('a1b2c3d4-e5f6-7890-abcd-ef1234567890').valid).toBe(true);
        expect(uuid.validate('invalid').valid).toBe(false);
      });
    });

    describe('I (Integer)', () => {
      it('should validate integers', () => {
        const validator = I();
        expect(validator.validate(42).valid).toBe(true);
        expect(validator.validate(3.14).valid).toBe(false);
      });

      it('should respect range constraints', () => {
        const validator = I(0, 100);
        expect(validator.validate(50).valid).toBe(true);
        expect(validator.validate(-1).valid).toBe(false);
        expect(validator.validate(101).valid).toBe(false);
      });
    });

    describe('N (Number)', () => {
      it('should validate numbers including floats', () => {
        const validator = N();
        expect(validator.validate(42).valid).toBe(true);
        expect(validator.validate(3.14).valid).toBe(true);
        expect(validator.validate('42').valid).toBe(false);
      });
    });

    describe('L (Long/BigInt)', () => {
      it('should validate bigint values', () => {
        const validator = L();
        expect(validator.validate(42n).valid).toBe(true);
        expect(validator.validate(9007199254740993n).valid).toBe(true);
        expect(validator.validate('not a number').valid).toBe(false);
      });

      it('should accept integer numbers and convert to bigint', () => {
        const validator = L();
        const result = validator.validate(42);
        expect(result.valid).toBe(true);
        if (result.valid) {
          expect(result.value).toBe(42n);
        }
      });
    });

    describe('Bytes (Binary)', () => {
      it('should validate Uint8Array values', () => {
        const validator = Bytes();
        expect(validator.validate(new Uint8Array([1, 2, 3])).valid).toBe(true);
        expect(validator.validate('not binary').valid).toBe(false);
      });

      it('should respect length constraints', () => {
        const validator = Bytes(2, 5);
        expect(validator.validate(new Uint8Array([1, 2])).valid).toBe(true);
        expect(validator.validate(new Uint8Array([1])).valid).toBe(false);
      });
    });

    describe('R (Regex)', () => {
      it('should validate strings matching pattern', () => {
        const validator = R(/^hello$/);
        expect(validator.validate('hello').valid).toBe(true);
        expect(validator.validate('world').valid).toBe(false);
      });
    });

    describe('C (Constant)', () => {
      it('should validate exact value', () => {
        const validator = C(42);
        expect(validator.validate(42).valid).toBe(true);
        expect(validator.validate(43).valid).toBe(false);
      });
    });
  });

  describe('special values', () => {
    describe('Null', () => {
      it('should validate null', () => {
        const validator = Null();
        expect(validator.validate(null).valid).toBe(true);
        expect(validator.validate(undefined).valid).toBe(false);
      });
    });

    describe('Undefined', () => {
      it('should validate undefined', () => {
        const validator = Undefined();
        expect(validator.validate(undefined).valid).toBe(true);
        expect(validator.validate(null).valid).toBe(false);
      });
    });

    describe('Inf (Infinity)', () => {
      it('should validate positive infinity', () => {
        const validator = Inf();
        expect(validator.validate(Infinity).valid).toBe(true);
        expect(validator.validate(-Infinity).valid).toBe(false);
      });
    });

    describe('NInf (NegativeInfinity)', () => {
      it('should validate negative infinity', () => {
        const validator = NInf();
        expect(validator.validate(-Infinity).valid).toBe(true);
        expect(validator.validate(Infinity).valid).toBe(false);
      });
    });

    describe('NaN', () => {
      it('should validate NaN', () => {
        const validator = NaN();
        expect(validator.validate(Number.NaN).valid).toBe(true);
        expect(validator.validate(0).valid).toBe(false);
      });
    });
  });

  describe('struct validator', () => {
    describe('O (Struct)', () => {
      it('should validate object structure', () => {
        const validator = O({
          name: U(1, 50),
          age: I(0, 150),
        });

        expect(validator.validate({ name: 'Alice', age: 30 }).valid).toBe(true);
        expect(validator.validate({ name: 'Bob' }).valid).toBe(false);
      });

      it('should support nested structures', () => {
        const validator = O({
          user: O({ name: U() }),
          count: I(),
        });

        expect(validator.validate({ user: { name: 'Alice' }, count: 5 }).valid).toBe(true);
      });

      it('should auto-wrap primitives in schema', () => {
        const config = O({
          version: 1,
          env: 'production',
          port: I(1, 65535),
        });

        expect(config.validate({ version: 1, env: 'production', port: 8080 }).valid).toBe(true);
        expect(config.validate({ version: 2, env: 'production', port: 8080 }).valid).toBe(false);
      });
    });
  });

  describe('combinators', () => {
    describe('Or (Alternation)', () => {
      it('should validate if any validator matches', () => {
        const validator = Or(U(), I());
        expect(validator.validate('hello').valid).toBe(true);
        expect(validator.validate(42).valid).toBe(true);
        expect(validator.validate(true).valid).toBe(false);
      });

      it('should auto-wrap string primitives in Constant', () => {
        const protocol = Or('http', 'https', 'ws', 'wss');
        expect(protocol.validate('http').valid).toBe(true);
        expect(protocol.validate('ftp').valid).toBe(false);
      });

      it('should auto-wrap number primitives in Constant', () => {
        const statusCode = Or(200, 201, 204, 404, 500);
        expect(statusCode.validate(200).valid).toBe(true);
        expect(statusCode.validate(403).valid).toBe(false);
      });
    });

    describe('Enum', () => {
      enum StringStatus {
        Pending = 'pending',
        Active = 'active',
        Completed = 'completed',
      }

      enum NumericDirection {
        Up = 0,
        Down = 1,
        Left = 2,
        Right = 3,
      }

      it('should validate string enum values', () => {
        const validator = Enum(StringStatus);
        expect(validator.validate('pending').valid).toBe(true);
        expect(validator.validate('invalid').valid).toBe(false);
      });

      it('should validate numeric enum values', () => {
        const validator = Enum(NumericDirection);
        expect(validator.validate(0).valid).toBe(true);
        expect(validator.validate(4).valid).toBe(false);
      });

      it('should generate valid enum values', () => {
        const { Generator } = require('@janus-validator/core');
        const validator = Enum(StringStatus);
        const generator = new Generator({ random: Math.random });
        const generated = generator.generate(validator.domain);
        expect(['pending', 'active', 'completed']).toContain(generated);
      });
    });

    describe('auto-wrapping enums in O', () => {
      enum Color {
        Red = 'red',
        Green = 'green',
        Blue = 'blue',
      }

      it('should auto-wrap string enums in O schema', () => {
        const schema = O({
          name: U(1, 50),
          color: Color,
        });

        expect(schema.validate({ name: 'Test', color: 'red' }).valid).toBe(true);
        expect(schema.validate({ name: 'Test', color: 'yellow' }).valid).toBe(false);
      });
    });

    describe('Seq (Sequence)', () => {
      it('should validate tuple-like arrays', () => {
        const validator = Seq(U(), I(), B());
        expect(validator.validate(['hello', 42, true]).valid).toBe(true);
        expect(validator.validate(['hello', 42]).valid).toBe(false);
      });

      it('should auto-wrap primitives', () => {
        const header = Seq('START', I(), 'END');
        expect(header.validate(['START', 42, 'END']).valid).toBe(true);
        expect(header.validate(['BEGIN', 42, 'END']).valid).toBe(false);
      });
    });
  });

  describe('quantifier functions', () => {
    describe('zeroOrMore', () => {
      it('should validate arrays of any length', () => {
        const validator = zeroOrMore(I(0, 10));
        expect(validator.validate([]).valid).toBe(true);
        expect(validator.validate([1, 2, 3]).valid).toBe(true);
        expect(validator.validate([1, 20, 3]).valid).toBe(false);
      });
    });

    describe('oneOrMore', () => {
      it('should require at least one element', () => {
        const validator = oneOrMore(U());
        expect(validator.validate(['a']).valid).toBe(true);
        expect(validator.validate([]).valid).toBe(false);
      });
    });

    describe('optional', () => {
      it('should allow 0 or 1 element', () => {
        const validator = optional(I());
        expect(validator.validate([]).valid).toBe(true);
        expect(validator.validate([42]).valid).toBe(true);
        expect(validator.validate([1, 2]).valid).toBe(false);
      });
    });

    describe('exactly', () => {
      it('should require exact count', () => {
        const validator = exactly(U(), 3);
        expect(validator.validate(['a', 'b', 'c']).valid).toBe(true);
        expect(validator.validate(['a', 'b']).valid).toBe(false);
      });
    });

    describe('atLeast', () => {
      it('should require minimum count', () => {
        const validator = atLeast(I(), 2);
        expect(validator.validate([1, 2]).valid).toBe(true);
        expect(validator.validate([1]).valid).toBe(false);
      });
    });

    describe('between', () => {
      it('should require count in range', () => {
        const validator = between(U(), 2, 4);
        expect(validator.validate(['a', 'b']).valid).toBe(true);
        expect(validator.validate(['a']).valid).toBe(false);
      });
    });
  });

  describe('type inference', () => {
    it('Or should infer union types', () => {
      const stringOrNumber = Or(U(), I());
      const strResult = stringOrNumber.validate('hello');
      const numResult = stringOrNumber.validate(42);
      expect(strResult.valid).toBe(true);
      expect(numResult.valid).toBe(true);
    });

    it('O (Struct) should infer object types', () => {
      const user = O({
        name: U(),
        age: I(),
        active: B(),
      });

      const result = user.validate({ name: 'Alice', age: 30, active: true });
      expect(result.valid).toBe(true);
      
      if (result.valid) {
        const name: string = result.value.name;
        const age: number = result.value.age;
        const active: boolean = result.value.active;
        expect(name).toBe('Alice');
        expect(age).toBe(30);
        expect(active).toBe(true);
      }
    });

    it('Seq should infer tuple types', () => {
      const tuple = Seq(U(), I(), B());
      const result = tuple.validate(['hello', 42, true]);
      expect(result.valid).toBe(true);
      
      if (result.valid) {
        const [str, num, bool] = result.value;
        expect(str).toBe('hello');
        expect(num).toBe(42);
        expect(bool).toBe(true);
      }
    });
  });

  describe('real-world usage examples', () => {
    it('should validate a user schema', () => {
      // Note: Use explicit character classes for portability (no \w, \d, \s)
      const User = O({
        id: I(1, 999999),
        username: U(3, 20),
        email: R(/^[A-Za-z0-9_.]+@[A-Za-z0-9_.]+\.[A-Za-z0-9_]+$/),
        age: I(0, 150),
        active: B(),
      });

      expect(User.validate({
        id: 123,
        username: 'alice',
        email: 'alice@example.com',
        age: 30,
        active: true,
      }).valid).toBe(true);
    });

    it('should validate an API response', () => {
      const Item = O({
        name: U(1, 100),
        price: N(0, 10000),
      });

      const Response = O({
        success: B(),
        items: oneOrMore(Item),
      });

      expect(Response.validate({
        success: true,
        items: [
          { name: 'Widget', price: 9.99 },
          { name: 'Gadget', price: 19.99 },
        ],
      }).valid).toBe(true);
    });
  });
});
