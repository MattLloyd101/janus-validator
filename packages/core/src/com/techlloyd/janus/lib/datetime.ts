/**
 * Date and time validators
 */

import { Regex } from '../combinators/Regex';
import { String as S, digits, chars } from '../combinators/String';
import { Integer } from '../combinators/Integer';
import { Struct } from '../combinators/Struct';
import { UnicodeString } from '../combinators/UnicodeString';

// ============================================================================
// Date formats
// ============================================================================

/**
 * ISO 8601 date (YYYY-MM-DD) with month/day validation
 */
export const ISODate = () => Regex(/^\d{4}-(0[1-9]|1[0-2])-(0[1-9]|[12]\d|3[01])$/);

/**
 * ISO 8601 datetime with timezone (full validation via regex)
 */
export const ISODateTime = () => Regex(/^\d{4}-(0[1-9]|1[0-2])-(0[1-9]|[12]\d|3[01])T([01]\d|2[0-3]):[0-5]\d:[0-5]\d(\.\d+)?(Z|[+-]([01]\d|2[0-3]):[0-5]\d)?$/);

/**
 * US date format (MM/DD/YYYY) with month/day validation
 */
export const USDate = () => Regex(/^(0[1-9]|1[0-2])\/(0[1-9]|[12]\d|3[01])\/\d{4}$/);

/**
 * European date format (DD/MM/YYYY) with day/month validation
 */
export const EUDate = () => Regex(/^(0[1-9]|[12]\d|3[01])\/(0[1-9]|1[0-2])\/\d{4}$/);

/**
 * Year (1000-9999)
 */
export const Year = () => Integer(1000, 9999);

/**
 * Month (1-12)
 */
export const Month = () => Integer(1, 12);

/**
 * Day of month (1-31)
 */
export const DayOfMonth = () => Integer(1, 31);

// ============================================================================
// Time formats
// ============================================================================

/**
 * 24-hour time (HH:MM) with hour/minute validation
 */
export const Time24 = () => Regex(/^([01]\d|2[0-3]):[0-5]\d$/);

/**
 * 24-hour time with seconds (HH:MM:SS) with validation
 */
export const Time24WithSeconds = () => Regex(/^([01]\d|2[0-3]):[0-5]\d:[0-5]\d$/);

/**
 * 12-hour time (HH:MM AM/PM) - uses regex for AM/PM validation
 */
export const Time12 = () => Regex(/^(0?[1-9]|1[0-2]):[0-5]\d\s?(AM|PM|am|pm)$/);

/**
 * Hour (0-23)
 */
export const Hour24 = () => Integer(0, 23);

/**
 * Hour (1-12)
 */
export const Hour12 = () => Integer(1, 12);

/**
 * Minute (0-59)
 */
export const Minute = () => Integer(0, 59);

/**
 * Second (0-59)
 */
export const Second = () => Integer(0, 59);

// ============================================================================
// Timezone
// ============================================================================

/**
 * IANA timezone (e.g., America/New_York, Europe/London)
 */
export const IANATimezone = () => S(
  chars('A-Za-z_', 1, 30),
  '/',
  chars('A-Za-z_', 1, 30)
);

/**
 * UTC offset (+/-HH:MM)
 */
export const UTCOffset = () => S(chars('+-', 1), digits(2), ':', digits(2));

// ============================================================================
// Duration
// ============================================================================

/**
 * ISO 8601 duration (P1Y2M3DT4H5M6S) - complex format requires regex
 */
export const ISODuration = () => Regex(/^P(\d+Y)?(\d+M)?(\d+D)?(T(\d+H)?(\d+M)?(\d+S)?)?$/);

/**
 * Duration in milliseconds
 */
export const DurationMs = () => Integer(0, Number.MAX_SAFE_INTEGER);

/**
 * Duration in seconds
 */
export const DurationSeconds = () => Integer(0, Number.MAX_SAFE_INTEGER);

// ============================================================================
// Date/time schemas
// ============================================================================

/**
 * Date range
 */
export const DateRange = () => Struct({
  start: ISODate(),
  end: ISODate(),
});

/**
 * DateTime range
 */
export const DateTimeRange = () => Struct({
  start: ISODateTime(),
  end: ISODateTime(),
});

/**
 * Scheduled event
 */
export const ScheduledEvent = () => Struct({
  name: UnicodeString(1, 200),
  startTime: ISODateTime(),
  endTime: ISODateTime(),
  timezone: IANATimezone(),
});

/**
 * Recurring schedule (cron-like) - complex format requires regex
 */
export const CronExpression = () => Regex(/^(\*|[0-5]?\d)\s+(\*|[01]?\d|2[0-3])\s+(\*|[1-9]|[12]\d|3[01])\s+(\*|[1-9]|1[0-2])\s+(\*|[0-6])$/);
