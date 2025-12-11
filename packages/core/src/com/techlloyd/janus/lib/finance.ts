/**
 * Financial validators - credit cards, currencies, banking
 */

import { S, N, R, O, Or, C, digits, upper, alphanumeric } from '../DSL';
import { UnicodeString } from '../combinators/UnicodeString';

// ============================================================================
// Credit Cards
// ============================================================================

/**
 * Credit card number (Luhn algorithm not validated, just format)
 * 13-19 digits with optional spaces/dashes
 */
export const CreditCardNumber = () => R(/^[\d\s-]{13,23}$/);

/**
 * Visa card (starts with 4, 13 or 16 digits)
 */
export const VisaCard = () => R(/^4\d{12}(\d{3})?$/);

/**
 * Mastercard (starts with 51-55 or 2221-2720)
 */
export const MasterCard = () => R(/^(5[1-5]\d{14}|2(2[2-9][1-9]|[3-6]\d{2}|7[01]\d|720)\d{12})$/);

/**
 * American Express (starts with 34 or 37)
 */
export const AmexCard = () => R(/^3[47]\d{13}$/);

/**
 * CVV/CVC (3-4 digits)
 */
export const CVV = () => S(digits(3, 4));

/**
 * Card expiry (MM/YY) with month validation
 */
export const CardExpiryShort = () => R(/^(0[1-9]|1[0-2])\/\d{2}$/);

/**
 * Card expiry (MM/YYYY) with month validation
 */
export const CardExpiryLong = () => R(/^(0[1-9]|1[0-2])\/\d{4}$/);

/**
 * Card expiry (MM/YY or MM/YYYY)
 */
export const CardExpiry = () => Or(CardExpiryShort(), CardExpiryLong());

/**
 * Full credit card info
 */
export const CreditCard = () => O({
  number: CreditCardNumber(),
  expiry: CardExpiry(),
  cvv: CVV(),
  name: UnicodeString(1, 100),
});

// ============================================================================
// Currency
// ============================================================================

/**
 * ISO 4217 currency code (USD, EUR, GBP, etc.)
 */
export const CurrencyCode = () => S(upper(3));

/**
 * Money amount (positive, up to 2 decimal places)
 */
export const MoneyAmount = () => R(/^\d+(\.\d{1,2})?$/);

/**
 * Price with optional negative (for refunds)
 */
export const Price = () => R(/^-?\d+(\.\d{1,2})?$/);

/**
 * Percentage (0-100 with up to 2 decimals)
 */
export const Percentage = () => N(0, 100);

/**
 * Money with currency
 */
export const Money = () => O({
  amount: N(0, Number.MAX_SAFE_INTEGER),
  currency: CurrencyCode(),
});

// ============================================================================
// Banking
// ============================================================================

/**
 * US routing number (9 digits)
 */
export const USRoutingNumber = () => S(digits(9));

/**
 * US bank account number (typically 8-17 digits)
 */
export const USBankAccountNumber = () => S(digits(8, 17));

/**
 * IBAN (International Bank Account Number)
 * Country code (2 letters) + check digits (2) + BBAN (11-30 alphanumeric)
 */
export const IBAN = () => S(upper(2), digits(2), alphanumeric(11, 30));

/**
 * SWIFT/BIC code (8 or 11 characters)
 */
export const SWIFT = () => R(/^[A-Z]{4}[A-Z]{2}[A-Z0-9]{2}([A-Z0-9]{3})?$/);

/**
 * US bank account
 */
export const USBankAccount = () => O({
  routingNumber: USRoutingNumber(),
  accountNumber: USBankAccountNumber(),
  accountType: Or(C('checking'), C('savings')),
});

// ============================================================================
// Tax IDs
// ============================================================================

/**
 * US SSN (Social Security Number): XXX-XX-XXXX
 */
export const SSNFormatted = () => S(digits(3), '-', digits(2), '-', digits(4));

/**
 * US SSN with optional dashes
 */
export const SSN = () => R(/^\d{3}-?\d{2}-?\d{4}$/);

/**
 * US EIN (Employer Identification Number): XX-XXXXXXX
 */
export const EINFormatted = () => S(digits(2), '-', digits(7));

/**
 * US EIN with optional dash
 */
export const EIN = () => R(/^\d{2}-?\d{7}$/);

/**
 * UK VAT number
 */
export const UKVAT = () => S('GB', digits(9, 12));

/**
 * EU VAT number (simplified)
 */
export const EUVAT = () => S(upper(2), alphanumeric(2, 12));

// ============================================================================
// Transactions
// ============================================================================

/**
 * Transaction schema
 */
export const Transaction = () => O({
  id: S(alphanumeric(1, 50)),
  amount: Money(),
  description: UnicodeString(0, 500),
  timestamp: ISOTimestamp(),
});

/**
 * ISO timestamp for transactions
 */
const ISOTimestamp = () => S(
  digits(4), '-', digits(2), '-', digits(2),
  'T',
  digits(2), ':', digits(2), ':', digits(2)
);

/**
 * Payment method
 */
export const PaymentMethod = () => O({
  type: Or(C('card'), C('bank'), C('paypal')),
  last4: S(digits(4)),
});
