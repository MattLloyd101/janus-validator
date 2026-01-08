/**
 * Network validators - URLs, IP addresses, domains, ports
 */

import { Regex } from '../combinators/Regex';
import { CompoundString as S, digits, hex, chars } from '../combinators/CompoundString';
import { Integer } from '../combinators/Integer';
import { Struct } from '../combinators/Struct';
import { Alternation } from '../combinators/Alternation';
import { Constant } from '../combinators/Constant';

// ============================================================================
// URLs
// ============================================================================

/**
 * HTTP/HTTPS URL
 */
export const URL = () => Regex(/^https?:\/\/[a-zA-Z0-9][-a-zA-Z0-9]*(\.[a-zA-Z0-9][-a-zA-Z0-9]*)*(:[0-9]+)?(\/[-a-zA-Z0-9_.~%]*)*(\?[-a-zA-Z0-9_.~%&=]*)?(#[-a-zA-Z0-9_.~%]*)?$/);

/**
 * Simple URL (less strict, more permissive)
 * Note: Uses explicit non-whitespace character class for portability
 */
export const SimpleURL = () =>
  Regex(/^https?:\/\/[A-Za-z0-9._~:/?#@!$&'()*+,;=%-]+$/);

/**
 * Secure URL (HTTPS only)
 */
export const SecureURL = () => Regex(/^https:\/\/[a-zA-Z0-9][-a-zA-Z0-9]*(\.[a-zA-Z0-9][-a-zA-Z0-9]*)*(:[0-9]+)?(\/[-a-zA-Z0-9_.~%]*)*(\?[-a-zA-Z0-9_.~%&=]*)?(#[-a-zA-Z0-9_.~%]*)?$/);

/**
 * WebSocket URL
 */
export const WebSocketURL = () => Regex(/^wss?:\/\/[a-zA-Z0-9][-a-zA-Z0-9]*(\.[a-zA-Z0-9][-a-zA-Z0-9]*)*(:[0-9]+)?(\/[-a-zA-Z0-9_.~%]*)*$/);

/**
 * FTP URL
 */
export const FTPURL = () => Regex(/^ftps?:\/\/[a-zA-Z0-9][-a-zA-Z0-9]*(\.[a-zA-Z0-9][-a-zA-Z0-9]*)*(:[0-9]+)?(\/[-a-zA-Z0-9_.~%]*)*$/);

// ============================================================================
// Domains
// ============================================================================

/**
 * Domain name (without protocol)
 */
export const Domain = () => Regex(/^[a-zA-Z0-9][-a-zA-Z0-9]*(\.[a-zA-Z0-9][-a-zA-Z0-9]*)+$/);

/**
 * Subdomain
 */
export const Subdomain = () => S(chars('a-zA-Z0-9-', 1, 63));

/**
 * Hostname (domain or IP)
 */
export const Hostname = () => Alternation.of(Domain(), IPv4());

// ============================================================================
// IP Addresses
// ============================================================================

/**
 * IPv4 address - validated format with regex for proper octet ranges
 */
export const IPv4 = () => Regex(/^((25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.){3}(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)$/);

/**
 * IPv4 simple format (for generation): X.X.X.X
 */
export const IPv4Simple = () => S(
  digits(1, 3), '.', digits(1, 3), '.', digits(1, 3), '.', digits(1, 3)
);

/**
 * IPv6 address (simplified) - complex format requires regex
 */
export const IPv6 = () => Regex(/^([0-9a-fA-F]{1,4}:){7}[0-9a-fA-F]{1,4}$|^::([0-9a-fA-F]{1,4}:){0,6}[0-9a-fA-F]{1,4}$|^([0-9a-fA-F]{1,4}:){1,6}:([0-9a-fA-F]{1,4})?$|^([0-9a-fA-F]{1,4}:){1,7}:$/);

/**
 * IPv6 full format (for generation): 8 groups of 4 hex digits
 */
export const IPv6Full = () => S(
  hex(4), ':', hex(4), ':', hex(4), ':', hex(4), ':',
  hex(4), ':', hex(4), ':', hex(4), ':', hex(4)
);

/**
 * IP address (v4 or v6)
 */
export const IPAddress = () => Alternation.of(IPv4(), IPv6());

/**
 * CIDR notation (IPv4) - requires regex for range validation
 */
export const CIDR = () => Regex(/^((25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.){3}(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\/(3[0-2]|[12]?[0-9])$/);

/**
 * Private IPv4 address ranges
 */
export const PrivateIPv4 = () => Regex(/^(10\.[0-9]{1,3}\.[0-9]{1,3}\.[0-9]{1,3})|(172\.(1[6-9]|2[0-9]|3[01])\.[0-9]{1,3}\.[0-9]{1,3})|(192\.168\.[0-9]{1,3}\.[0-9]{1,3})$/);

// ============================================================================
// Ports
// ============================================================================

/**
 * Port number (1-65535)
 */
export const Port = () => Integer(1, 65535);

/**
 * Well-known port (1-1023)
 */
export const WellKnownPort = () => Integer(1, 1023);

/**
 * Registered port (1024-49151)
 */
export const RegisteredPort = () => Integer(1024, 49151);

/**
 * Dynamic/private port (49152-65535)
 */
export const DynamicPort = () => Integer(49152, 65535);

// ============================================================================
// MAC Address
// ============================================================================

/**
 * MAC address with colons: XX:XX:XX:XX:XX:XX (case-insensitive hex)
 */
export const MACAddressColon = () => Regex(/^[0-9A-Fa-f]{2}:[0-9A-Fa-f]{2}:[0-9A-Fa-f]{2}:[0-9A-Fa-f]{2}:[0-9A-Fa-f]{2}:[0-9A-Fa-f]{2}$/);

/**
 * MAC address with hyphens: XX-XX-XX-XX-XX-XX (case-insensitive hex)
 */
export const MACAddressHyphen = () => Regex(/^[0-9A-Fa-f]{2}-[0-9A-Fa-f]{2}-[0-9A-Fa-f]{2}-[0-9A-Fa-f]{2}-[0-9A-Fa-f]{2}-[0-9A-Fa-f]{2}$/);

/**
 * MAC address (colon or hyphen separated)
 */
export const MACAddress = () => Alternation.of(MACAddressColon(), MACAddressHyphen());

// ============================================================================
// Network schemas
// ============================================================================

/**
 * Host with port
 */
export const HostPort = () => Struct({
  host: Hostname(),
  port: Port(),
});

/**
 * Server configuration
 */
export const ServerConfig = () => Struct({
  host: Hostname(),
  port: Port(),
  protocol: Alternation.of(Constant('http'), Constant('https'), Constant('ws'), Constant('wss')),
});
