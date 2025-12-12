import { BaseValidator } from '../Validator';
import { ValidationResult } from '../ValidationResult';
import { BytesDomain, DomainType } from '../Domain';

/**
 * Validator for variable-length binary data (Uint8Array)
 * 
 * @example
 * ```typescript
 * const binaryData = Bytes(0, 100);
 * binaryData.validate(new Uint8Array([1, 2, 3])); // valid
 * binaryData.validate(Buffer.from([1, 2, 3]));    // valid (Node.js Buffer)
 * ```
 */
export class BytesValidator extends BaseValidator<Uint8Array> {
  public readonly domain: BytesDomain;

  constructor(
    public readonly minLength: number = 0,
    public readonly maxLength: number = 1024
  ) {
    super();
    if (minLength < 0) {
      throw new Error('minLength must be non-negative');
    }
    if (maxLength < minLength) {
      throw new Error('maxLength must be greater than or equal to minLength');
    }
    this.domain = {
      type: DomainType.BYTES_DOMAIN,
      minLength,
      maxLength,
    };
  }

  /**
   * Checks if the input is a Buffer (Node.js)
   */
  private isBuffer(input: unknown): input is Buffer {
    return typeof Buffer !== 'undefined' && Buffer.isBuffer(input);
  }

  validate(input: unknown): ValidationResult<Uint8Array> {
    // Accept Uint8Array directly
    if (input instanceof Uint8Array) {
      const length = input.length;
      if (length < this.minLength) {
        return this.error(`Byte array length ${length} is less than minimum ${this.minLength}`);
      }
      if (length > this.maxLength) {
        return this.error(`Byte array length ${length} is greater than maximum ${this.maxLength}`);
      }
      return this.success(input);
    }

    // Accept Node.js Buffer and convert to Uint8Array
    if (this.isBuffer(input)) {
      const uint8 = new Uint8Array(input);
      const length = uint8.length;
      if (length < this.minLength) {
        return this.error(`Byte array length ${length} is less than minimum ${this.minLength}`);
      }
      if (length > this.maxLength) {
        return this.error(`Byte array length ${length} is greater than maximum ${this.maxLength}`);
      }
      return this.success(uint8);
    }

    return this.error(`Expected Uint8Array or Buffer, got ${typeof input}`);
  }
}

/**
 * Creates a validator for variable-length binary data (Uint8Array)
 */
export function Bytes(minLength: number = 0, maxLength: number = 1024): BytesValidator {
  return new BytesValidator(minLength, maxLength);
}
