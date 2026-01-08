/**
 * Realistic value generators for common use cases
 * 
 * These presets override default generation to provide realistic test data.
 * They use CustomGeneratorDomain internally, which means:
 * - Validation still uses the semantic domain
 * - Generation produces realistic values
 * - Schema export strips the generator (preserves semantic domain)
 */

import {
  Regex,
  CompoundString as S,
  digits,
  upper,
  letters,
  Float,
  UnicodeString,
  fromValues,
  templateGenerator,
  combineGenerators,
} from '@janus-validator/core';

// ============================================================================
// Names
// ============================================================================

const FIRST_NAMES = [
  'Alice', 'Bob', 'Charlie', 'Diana', 'Eve', 'Frank', 'Grace', 'Henry',
  'Iris', 'Jack', 'Kate', 'Liam', 'Mia', 'Noah', 'Olivia', 'Peter',
  'Quinn', 'Rose', 'Sam', 'Tina', 'Uma', 'Victor', 'Wendy', 'Xavier',
  'Yara', 'Zach', 'Emma', 'James', 'Sophia', 'William', 'Ava', 'Benjamin',
  'Isabella', 'Lucas', 'Amelia', 'Mason', 'Harper', 'Ethan', 'Evelyn', 'Alexander',
];

const LAST_NAMES = [
  'Smith', 'Johnson', 'Williams', 'Brown', 'Jones', 'Garcia', 'Miller', 'Davis',
  'Rodriguez', 'Martinez', 'Hernandez', 'Lopez', 'Gonzalez', 'Wilson', 'Anderson',
  'Thomas', 'Taylor', 'Moore', 'Jackson', 'Martin', 'Lee', 'Perez', 'Thompson',
  'White', 'Harris', 'Sanchez', 'Clark', 'Ramirez', 'Lewis', 'Robinson',
];

/**
 * First name with realistic values
 */
export const FirstName = () => fromValues(S(letters(1, 50)), FIRST_NAMES);

/**
 * Last name with realistic values
 */
export const LastName = () => fromValues(S(letters(1, 50)), LAST_NAMES);

/**
 * Full name (first + last)
 */
export const FullName = () => templateGenerator(UnicodeString(1, 100), (pick) => 
  `${pick(FIRST_NAMES)} ${pick(LAST_NAMES)}`
);

// ============================================================================
// Usernames and Handles
// ============================================================================

const USERNAME_ADJECTIVES = [
  'happy', 'clever', 'quick', 'brave', 'cool', 'dark', 'epic', 'fast',
  'great', 'hyper', 'iron', 'jade', 'keen', 'lucky', 'mega', 'neo',
  'omega', 'prime', 'quick', 'royal', 'super', 'true', 'ultra', 'vivid',
];

const USERNAME_NOUNS = [
  'tiger', 'eagle', 'wolf', 'bear', 'hawk', 'lion', 'fox', 'shark',
  'dragon', 'phoenix', 'ninja', 'knight', 'wizard', 'ranger', 'hunter',
  'rider', 'pilot', 'gamer', 'coder', 'hacker', 'master', 'legend',
];

/**
 * Username with realistic gaming-style names
 */
export const RealisticUsername = () => templateGenerator(
  Regex(/^[a-zA-Z][a-zA-Z0-9_]{2,19}$/),
  (pick, rng) => {
    const adj = pick(USERNAME_ADJECTIVES);
    const noun = pick(USERNAME_NOUNS);
    const num = Math.floor(rng.random() * 100);
    return `${adj}_${noun}${num}`;
  }
);

// ============================================================================
// Emails
// ============================================================================

const EMAIL_DOMAINS = [
  'gmail.com', 'yahoo.com', 'outlook.com', 'hotmail.com', 'icloud.com',
  'protonmail.com', 'mail.com', 'aol.com',
];

const CORPORATE_DOMAINS = [
  'company.com', 'acme.com', 'corp.io', 'tech.co', 'enterprise.com',
  'startup.io', 'business.net', 'global.org',
];

/**
 * Realistic personal email addresses
 */
export const RealisticEmail = () => templateGenerator(
  Regex(/^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$/),
  (pick, rng) => {
    const first = pick(FIRST_NAMES).toLowerCase();
    const last = pick(LAST_NAMES).toLowerCase();
    const domain = pick(EMAIL_DOMAINS);
    const style = Math.floor(rng.random() * 4);
    
    switch (style) {
      case 0: return `${first}.${last}@${domain}`;
      case 1: return `${first}${last}@${domain}`;
      case 2: return `${first}${Math.floor(rng.random() * 100)}@${domain}`;
      default: return `${first}_${last}@${domain}`;
    }
  }
);

/**
 * Realistic corporate email addresses
 */
export const CorporateEmailPreset = () => templateGenerator(
  Regex(/^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$/),
  (pick) => {
    const first = pick(FIRST_NAMES).toLowerCase();
    const last = pick(LAST_NAMES).toLowerCase();
    const domain = pick(CORPORATE_DOMAINS);
    return `${first}.${last}@${domain}`;
  }
);

// ============================================================================
// Addresses
// ============================================================================

const STREET_NAMES = [
  'Main', 'Oak', 'Maple', 'Cedar', 'Elm', 'Pine', 'Washington', 'Lincoln',
  'Park', 'Lake', 'Hill', 'River', 'Forest', 'Valley', 'Spring', 'Sunset',
];

const STREET_TYPES = ['St', 'Ave', 'Blvd', 'Dr', 'Ln', 'Rd', 'Way', 'Ct'];

const US_CITIES = [
  'New York', 'Los Angeles', 'Chicago', 'Houston', 'Phoenix', 'Philadelphia',
  'San Antonio', 'San Diego', 'Dallas', 'San Jose', 'Austin', 'Seattle',
  'Denver', 'Boston', 'Portland', 'Atlanta', 'Miami', 'Minneapolis',
];

const US_STATES = [
  'AL', 'AK', 'AZ', 'AR', 'CA', 'CO', 'CT', 'DE', 'FL', 'GA',
  'HI', 'ID', 'IL', 'IN', 'IA', 'KS', 'KY', 'LA', 'ME', 'MD',
  'MA', 'MI', 'MN', 'MS', 'MO', 'MT', 'NE', 'NV', 'NH', 'NJ',
  'NM', 'NY', 'NC', 'ND', 'OH', 'OK', 'OR', 'PA', 'RI', 'SC',
  'SD', 'TN', 'TX', 'UT', 'VT', 'VA', 'WA', 'WV', 'WI', 'WY',
];

/**
 * Realistic US street address
 */
export const RealisticStreetAddress = () => templateGenerator(
  UnicodeString(1, 100),
  (pick, rng) => {
    const num = Math.floor(rng.random() * 9999) + 1;
    const street = pick(STREET_NAMES);
    const type = pick(STREET_TYPES);
    return `${num} ${street} ${type}`;
  }
);

/**
 * Realistic US city
 */
export const RealisticCity = () => fromValues(UnicodeString(1, 50), US_CITIES);

/**
 * Realistic US state code
 */
export const RealisticState = () => fromValues(
  S(upper(2)),
  US_STATES
);

/**
 * Realistic US ZIP code
 */
export const RealisticZipCode = () => templateGenerator(
  Regex(/^[0-9]{5}(-[0-9]{4})?$/),
  (pick, rng) => {
    const zip = String(Math.floor(rng.random() * 90000) + 10000);
    // 30% chance of ZIP+4
    if (rng.random() < 0.3) {
      const ext = String(Math.floor(rng.random() * 9000) + 1000);
      return `${zip}-${ext}`;
    }
    return zip;
  }
);

// ============================================================================
// Phone Numbers
// ============================================================================

/**
 * Realistic US phone number
 */
export const RealisticUSPhone = () => templateGenerator(
  Regex(/^(\([0-9]{3}\)[ ]?|[0-9]{3}[-.]?)[0-9]{3}[-.]?[0-9]{4}$/),
  (pick, rng) => {
    const area = Math.floor(rng.random() * 800) + 200; // 200-999
    const exchange = Math.floor(rng.random() * 800) + 200;
    const subscriber = Math.floor(rng.random() * 9000) + 1000;
    
    const formats = [
      `(${area}) ${exchange}-${subscriber}`,
      `${area}-${exchange}-${subscriber}`,
      `${area}.${exchange}.${subscriber}`,
    ];
    return pick(formats);
  }
);

// ============================================================================
// Companies
// ============================================================================

const COMPANY_NAMES = [
  'Acme', 'Globex', 'Initech', 'Umbrella', 'Cyberdyne', 'Stark', 'Wayne',
  'Oscorp', 'LexCorp', 'Massive', 'Dynamic', 'Hooli', 'Pied', 'Piedmont',
];

const COMPANY_SUFFIXES = ['Inc', 'Corp', 'LLC', 'Ltd', 'Co', 'Group', 'Solutions'];

/**
 * Realistic company name
 */
export const CompanyName = () => templateGenerator(
  UnicodeString(1, 100),
  (pick) => `${pick(COMPANY_NAMES)} ${pick(COMPANY_SUFFIXES)}`
);

// ============================================================================
// Products and Descriptions
// ============================================================================

const PRODUCT_ADJECTIVES = ['Premium', 'Deluxe', 'Pro', 'Ultra', 'Elite', 'Classic', 'Essential'];
const PRODUCT_TYPES = ['Widget', 'Gadget', 'Device', 'Tool', 'Kit', 'System', 'Package'];

/**
 * Realistic product name
 */
export const ProductName = () => templateGenerator(
  UnicodeString(1, 100),
  (pick) => `${pick(PRODUCT_ADJECTIVES)} ${pick(PRODUCT_TYPES)}`
);

const LOREM_WORDS = [
  'lorem', 'ipsum', 'dolor', 'sit', 'amet', 'consectetur', 'adipiscing', 'elit',
  'sed', 'do', 'eiusmod', 'tempor', 'incididunt', 'ut', 'labore', 'et', 'dolore',
  'magna', 'aliqua', 'enim', 'ad', 'minim', 'veniam', 'quis', 'nostrud',
];

/**
 * Lorem ipsum style text generator
 */
export const LoremIpsum = (minWords: number = 10, maxWords: number = 50) => 
  templateGenerator(UnicodeString(minWords, maxWords * 10), (pick, rng) => {
    const wordCount = Math.floor(rng.random() * (maxWords - minWords + 1)) + minWords;
    const words: string[] = [];
    for (let i = 0; i < wordCount; i++) {
      words.push(pick(LOREM_WORDS));
    }
    // Capitalize first word and add period
    words[0] = words[0].charAt(0).toUpperCase() + words[0].slice(1);
    return words.join(' ') + '.';
  });

// ============================================================================
// Dates and Times
// ============================================================================

/**
 * Realistic date in the past (within last 5 years)
 */
export const RecentDate = () => templateGenerator(
  S(digits(4), '-', digits(2), '-', digits(2)),
  (pick, rng) => {
    const now = new Date();
    const pastDays = Math.floor(rng.random() * 365 * 5); // up to 5 years ago
    const date = new Date(now.getTime() - pastDays * 24 * 60 * 60 * 1000);
    return date.toISOString().split('T')[0];
  }
);

/**
 * Realistic date in the future (within next 2 years)
 */
export const FutureDate = () => templateGenerator(
  S(digits(4), '-', digits(2), '-', digits(2)),
  (pick, rng) => {
    const now = new Date();
    const futureDays = Math.floor(rng.random() * 365 * 2) + 1; // 1 day to 2 years
    const date = new Date(now.getTime() + futureDays * 24 * 60 * 60 * 1000);
    return date.toISOString().split('T')[0];
  }
);

// ============================================================================
// Money
// ============================================================================

/**
 * Realistic price (weighted toward common price points)
 */
export const RealisticPrice = () => combineGenerators(
  Float(0, 10000),
  [
    (rng) => Math.floor(rng.random() * 20) + 0.99, // $0.99 - $19.99
    (rng) => Math.floor(rng.random() * 50) + 19.99, // $19.99 - $69.99
    (rng) => Math.floor(rng.random() * 100) + 49.99, // $49.99 - $149.99
    (rng) => Math.floor(rng.random() * 500) + 99.99, // $99.99 - $599.99
  ]
);
