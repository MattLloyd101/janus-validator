/** @type {import('ts-jest').JestConfigWithTsJest} */
module.exports = {
  preset: 'ts-jest',
  testEnvironment: 'node',
  roots: ['<rootDir>/tests'],
  moduleNameMapper: {
    '^@/(.*)$': '<rootDir>/src/$1',
    '^@janus-validator/domain$': '<rootDir>/../domain/src/index.ts'
  },
  coverageThreshold: {
    global: {
      branches: 95,
      functions: 95,
      lines: 100,
      statements: 95,
    },
  },
  testMatch: ['**/*.test.ts'],
  transform: {
    '^.+\\.tsx?$': [
      'ts-jest',
      {
        tsconfig: 'tests/tsconfig.json',
      },
    ],
  },
};
