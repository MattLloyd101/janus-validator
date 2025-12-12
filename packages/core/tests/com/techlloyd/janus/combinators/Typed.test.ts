import { Typed, As } from '@/com/techlloyd/janus/combinators/Typed';
import { Struct } from '@/com/techlloyd/janus/combinators/Struct';
import { UnicodeString } from '@/com/techlloyd/janus/combinators/UnicodeString';
import { Integer } from '@/com/techlloyd/janus/combinators/Integer';
import { Boolean } from '@/com/techlloyd/janus/combinators/Boolean';
import { Alternation } from '@/com/techlloyd/janus/combinators/Alternation';
import { Null } from '@/com/techlloyd/janus/combinators/Null';
import { Generator } from '@/com/techlloyd/janus/Generator';

// Test interfaces
interface Address {
  street: string;
  city: string;
  zip: string;
}

interface User {
  name: string;
  age: number;
  active: boolean;
}

interface UserWithAddress {
  name: string;
  address: Address;
}

describe('Typed', () => {
  describe('basic usage', () => {
    it('should type the output as the specified interface', () => {
      const userValidator = Typed<User>()(Struct({
        name: UnicodeString(1, 100),
        age: Integer(0, 150),
        active: Boolean(),
      }));

      const result = userValidator.validate({
        name: 'Alice',
        age: 30,
        active: true,
      });

      expect(result.valid).toBe(true);
      if (result.valid) {
        // TypeScript knows this is User
        const user: User = result.value;
        expect(user.name).toBe('Alice');
        expect(user.age).toBe(30);
        expect(user.active).toBe(true);
      }
    });

    it('should work with nested interfaces by composing typed validators', () => {
      // Create a reusable typed Address validator
      const addressValidator = Typed<Address>()(Struct({
        street: UnicodeString(1, 200),
        city: UnicodeString(1, 100),
        zip: UnicodeString(5, 5),
      }));

      // Compose it into the UserWithAddress validator
      const userValidator = Typed<UserWithAddress>()(Struct({
        name: UnicodeString(1, 100),
        address: addressValidator,  // Reuse the typed validator
      }));

      const result = userValidator.validate({
        name: 'Bob',
        address: {
          street: '123 Main St',
          city: 'NYC',
          zip: '10001',
        },
      });

      expect(result.valid).toBe(true);
      if (result.valid) {
        const user: UserWithAddress = result.value;
        expect(user.address.city).toBe('NYC');
      }

      // The address validator can also be used standalone
      const addressResult = addressValidator.validate({
        street: '456 Oak Ave',
        city: 'LA',
        zip: '90001',
      });
      expect(addressResult.valid).toBe(true);
      if (addressResult.valid) {
        const address: Address = addressResult.value;
        expect(address.city).toBe('LA');
      }
    });

    it('should fail validation when data is invalid', () => {
      const userValidator = Typed<User>()(Struct({
        name: UnicodeString(1, 100),
        age: Integer(0, 150),
        active: Boolean(),
      }));

      const result = userValidator.validate({
        name: 'Alice',
        age: 'not a number',
        active: true,
      });

      expect(result.valid).toBe(false);
    });
  });

  describe('As alias', () => {
    it('should work the same as Typed', () => {
      const userValidator = As<User>()(Struct({
        name: UnicodeString(1, 100),
        age: Integer(),
        active: Boolean(),
      }));

      const result = userValidator.validate({
        name: 'Charlie',
        age: 25,
        active: false,
      });

      expect(result.valid).toBe(true);
      if (result.valid) {
        const user: User = result.value;
        expect(user.name).toBe('Charlie');
      }
    });
  });

  describe('with union types', () => {
    it('should work with Alternation', () => {
      type StringOrNumber = string | number;
      
      const validator = Typed<StringOrNumber>()(
        Alternation.of(UnicodeString(1, 100), Integer())
      );

      expect(validator.validate('hello').valid).toBe(true);
      expect(validator.validate(42).valid).toBe(true);
      expect(validator.validate(true).valid).toBe(false);
    });

    it('should work with nullable types', () => {
      type NullableString = string | null;
      
      const validator = Typed<NullableString>()(
        Alternation.of(UnicodeString(1, 100), Null())
      );

      expect(validator.validate('hello').valid).toBe(true);
      expect(validator.validate(null).valid).toBe(true);
      expect(validator.validate(undefined).valid).toBe(false);
    });
  });

  describe('generation', () => {
    it('should preserve domain for generation', () => {
      const userValidator = Typed<User>()(Struct({
        name: UnicodeString(1, 50),
        age: Integer(0, 150),
        active: Boolean(),
      }));

      const generator = new Generator({ random: Math.random });
      
      for (let i = 0; i < 10; i++) {
        const user: User = generator.generate(userValidator.domain);
        
        expect(typeof user.name).toBe('string');
        expect(typeof user.age).toBe('number');
        expect(typeof user.active).toBe('boolean');
        
        // Generated values should pass validation
        expect(userValidator.validate(user).valid).toBe(true);
      }
    });
  });

  describe('practical usage patterns', () => {
    it('should allow passing validated data to typed functions', () => {
      interface ApiRequest {
        userId: number;
        action: string;
      }

      function processRequest(req: ApiRequest): string {
        return `Processing ${req.action} for user ${req.userId}`;
      }

      const requestValidator = Typed<ApiRequest>()(Struct({
        userId: Integer(1, 1000000),
        action: UnicodeString(1, 50),
      }));

      const result = requestValidator.validate({
        userId: 123,
        action: 'login',
      });

      expect(result.valid).toBe(true);
      if (result.valid) {
        // Can pass directly to typed function
        const output = processRequest(result.value);
        expect(output).toBe('Processing login for user 123');
      }
    });
  });
});

