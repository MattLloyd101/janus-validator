import { Validator, BaseValidator } from '../../Validator';
import { ValidationResult } from '../../ValidationResult';
import { Domain } from '../../Domain';

/**
 * Context passed to superRefine callbacks.
 * 
 * Use this context to report multiple validation issues.
 */
export interface RefinementContext {
  /** Add a validation issue */
  addIssue: (issue: RefinementIssue) => void;
  /** Current path (for nested validation) */
  path: (string | number)[];
}

/**
 * A validation issue reported during superRefine.
 */
export interface RefinementIssue {
  /** Human-readable error message */
  message: string;
  /** Optional error code for i18n */
  code?: string;
  /** Optional path to the problematic field */
  path?: (string | number)[];
}

/**
 * Wrapper validator for complex refinements that may produce multiple issues.
 * 
 * Unlike simple `RefineValidator`, this allows collecting multiple validation
 * issues in a single pass, useful for comprehensive error reporting.
 * 
 * **Note:** Refinements do NOT affect the domain. Generated values may
 * fail refinement checks.
 * 
 * @typeParam T - The validated type
 * @typeParam D - The inner domain type
 * 
 * @example
 * ```typescript
 * const passwordValidator = new SuperRefineValidator(
 *   UnicodeString(8, 100),
 *   (value, ctx) => {
 *     if (!/[A-Z]/.test(value)) {
 *       ctx.addIssue({ message: 'Must contain uppercase letter' });
 *     }
 *     if (!/[0-9]/.test(value)) {
 *       ctx.addIssue({ message: 'Must contain digit' });
 *     }
 *   }
 * );
 * ```
 */
export class SuperRefineValidator<T, D extends Domain<T>> extends BaseValidator<T, D> {
  public readonly domain: D;

  constructor(
    private readonly inner: Validator<T, D>,
    private readonly refinement: (value: T, ctx: RefinementContext) => void
  ) {
    super();
    this.domain = inner.domain;
  }

  validate(value: unknown): ValidationResult<T> {
    // First run inner validation
    const innerResult = this.inner.validate(value);
    if (!innerResult.valid) {
      return innerResult;
    }

    // Collect refinement issues
    const issues: RefinementIssue[] = [];
    const ctx: RefinementContext = {
      addIssue: (issue) => issues.push(issue),
      path: [],
    };

    this.refinement(innerResult.value, ctx);

    if (issues.length > 0) {
      // Combine issues into error message
      const errorMsg = issues
        .map(i => i.path?.length ? `${i.path.join('.')}: ${i.message}` : i.message)
        .join('; ');
      return this.error(errorMsg);
    }

    return innerResult;
  }
}

/**
 * Adds complex custom validation with multiple potential issues.
 * 
 * @param validator The inner validator
 * @param refinement Function that calls ctx.addIssue() for each problem
 * @returns A new validator that collects all refinement issues
 * 
 * @example
 * ```typescript
 * const password = superRefine(U(8, 100), (value, ctx) => {
 *   if (!/[A-Z]/.test(value)) {
 *     ctx.addIssue({ message: 'Must contain uppercase letter' });
 *   }
 *   if (!/[0-9]/.test(value)) {
 *     ctx.addIssue({ message: 'Must contain digit' });
 *   }
 * });
 * 
 * // Cross-field validation
 * const registration = superRefine(
 *   Struct({ password: U(), confirm: U() }),
 *   (value, ctx) => {
 *     if (value.password !== value.confirm) {
 *       ctx.addIssue({ message: 'Passwords must match', path: ['confirm'] });
 *     }
 *   }
 * );
 * ```
 */
export function superRefine<T, D extends Domain<T>>(
  validator: Validator<T, D>,
  refinement: (value: T, ctx: RefinementContext) => void
): SuperRefineValidator<T, D> {
  return new SuperRefineValidator(validator, refinement);
}
