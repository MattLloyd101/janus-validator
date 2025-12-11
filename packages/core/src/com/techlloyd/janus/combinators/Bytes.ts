import { Validator, ValidationResult, BytesDomain, DomainType } from '../index';

/**
 * Creates a domain for binary data (Uint8Array)
 */
function bytesDomain(minLength: number, maxLength: number): BytesDomain {
  return {
    type: DomainType.BYTES_DOMAIN,
    minLength,
    maxLength,
  };
}

/**
 * Checks if the input is a valid Uint8Array or can be treated as binary data
 */
function isUint8Array(input: unknown): input is Uint8Array {
  return input instanceof Uint8Array;
}

/**
 * Checks if the input is a Buffer (Node.js)
 */
function isBuffer(input: unknown): input is Buffer {
  return typeof Buffer !== 'undefined' && Buffer.isBuffer(input);
}

/**
 * Creates a validator for variable-length binary data (Uint8Array)
 * 
 * @param minLength - Minimum byte length (default: 0)
 * @param maxLength - Maximum byte length (default: 1024)
 * @returns A validator for Uint8Array values
 * 
 * @example
 * ```typescript
 * const binaryData = Bytes(0, 100);
 * binaryData.validate(new Uint8Array([1, 2, 3])); // valid
 * binaryData.validate(Buffer.from([1, 2, 3]));    // valid (Node.js Buffer)
 * ```
 */
export function Bytes(minLength: number = 0, maxLength: number = 1024): Validator<Uint8Array> {
  if (minLength < 0) {
    throw new Error('minLength must be non-negative');
  }
  if (maxLength < minLength) {
    throw new Error('maxLength must be greater than or equal to minLength');
  }

  return {
    validate: (input: unknown): ValidationResult<Uint8Array> => {
      // Accept Uint8Array directly
      if (isUint8Array(input)) {
        const length = input.length;
        if (length < minLength) {
          return {
            valid: false,
            error: `Byte array length ${length} is less than minimum ${minLength}`,
          };
        }
        if (length > maxLength) {
          return {
            valid: false,
            error: `Byte array length ${length} is greater than maximum ${maxLength}`,
          };
        }
        return { valid: true, value: input };
      }

      // Accept Node.js Buffer and convert to Uint8Array
      if (isBuffer(input)) {
        const uint8 = new Uint8Array(input);
        const length = uint8.length;
        if (length < minLength) {
          return {
            valid: false,
            error: `Byte array length ${length} is less than minimum ${minLength}`,
          };
        }
        if (length > maxLength) {
          return {
            valid: false,
            error: `Byte array length ${length} is greater than maximum ${maxLength}`,
          };
        }
        return { valid: true, value: uint8 };
      }

      return {
        valid: false,
        error: `Expected Uint8Array or Buffer, got ${typeof input}`,
      };
    },
    domain: bytesDomain(minLength, maxLength),
  };
}

