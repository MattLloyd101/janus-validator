import { FiniteDomain } from '@/com/techlloyd/janus/Domain';

import { Integer } from '@/com/techlloyd/janus/combinators/Integer';
import { Long } from '@/com/techlloyd/janus/combinators/Long';
import { Bytes } from '@/com/techlloyd/janus/combinators/Bytes';
import { Struct } from '@/com/techlloyd/janus/combinators/Struct';
import { Alternation } from '@/com/techlloyd/janus/combinators/Alternation';
import { Undefined } from '@/com/techlloyd/janus/combinators/Undefined';
import { UnicodeString } from '@/com/techlloyd/janus/combinators/UnicodeString';
import { Quantifier } from '@/com/techlloyd/janus/combinators/Quantifier';
import { Sequence } from '@/com/techlloyd/janus/combinators/Sequence';
import { digits, alphanumeric, String as CompoundString } from '@/com/techlloyd/janus/combinators/String';
import { Regex } from '@/com/techlloyd/janus/combinators/Regex';

describe('Domain.encapsulates', () => {
  it('works for FINITE_DOMAIN', () => {
    const a: FiniteDomain<number> = new FiniteDomain([1, 2]);
    const b: FiniteDomain<number> = new FiniteDomain([0, 1, 2, 3]);
    const c: FiniteDomain<number> = new FiniteDomain([1]);

    expect(b.encapsulates(a).result).toBe('true');
    expect(c.encapsulates(a).result).toBe('false');
  });

  it('works for CONTIGUOUS_DOMAIN (Integer)', () => {
    const a = Integer(0, 5).domain;
    const b = Integer(0, 10).domain;
    const c = Integer(1, 10).domain;

    expect(b.encapsulates(a).result).toBe('true');
    expect(c.encapsulates(a).result).toBe('false');
  });

  it('works for BIGINT_DOMAIN (Long)', () => {
    const a = Long(0n, 5n).domain;
    const b = Long(0n, 10n).domain;
    const c = Long(1n, 10n).domain;

    expect(b.encapsulates(a).result).toBe('true');
    expect(c.encapsulates(a).result).toBe('false');
  });

  it('works for BYTES_DOMAIN', () => {
    const a = Bytes(2, 4).domain;
    const b = Bytes(1, 10).domain;
    const c = Bytes(3, 10).domain;

    expect(b.encapsulates(a).result).toBe('true');
    expect(c.encapsulates(a).result).toBe('false');
  });

  it('works for SEQUENCE_DOMAIN', () => {
    const a = new Sequence(Integer(0, 5), UnicodeString(1, 5)).domain;
    const b = new Sequence(Integer(0, 10), UnicodeString(1, 10)).domain;
    const c = new Sequence(Integer(1, 10), UnicodeString(1, 10)).domain;

    expect(b.encapsulates(a).result).toBe('true');
    expect(c.encapsulates(a).result).toBe('false');
  });

  it('works for QUANTIFIER_DOMAIN', () => {
    const a = new Quantifier(Integer(0, 5), 0, 5).domain;
    const b = new Quantifier(Integer(0, 10), 0, 10).domain;
    const c = new Quantifier(Integer(0, 10), 1, 10).domain;

    expect(b.encapsulates(a).result).toBe('true');
    expect(c.encapsulates(a).result).toBe('false');
  });

  it('works for ALTERNATION_DOMAIN (normalizes nested alternations)', () => {
    const a = Alternation.of(Integer(0, 1), Integer(10, 11)).domain;
    const b = Alternation.of(Alternation.of(Integer(0, 1), Integer(10, 11)), Integer(100, 101)).domain;

    expect(b.encapsulates(a).result).toBe('true');
  });

  it('works for STRUCT_DOMAIN and strictness', () => {
    const oldNonStrict = Struct({ a: Integer(0, 5) }, false).domain;
    const newStrict = Struct({ a: Integer(0, 10) }, true).domain;

    // Tightening strictness is not backwards compatible.
    expect(newStrict.encapsulates(oldNonStrict).result).toBe('false');
  });

  it('treats newly-added struct fields as compatible only if they accept undefined', () => {
    const oldSchema = Struct({ a: Integer(0, 5) }, false).domain;
    const newSchemaOptional = Struct(
      { a: Integer(0, 10), b: Alternation.of(Undefined(), UnicodeString(1, 10)) },
      false
    ).domain;
    const newSchemaRequired = Struct({ a: Integer(0, 10), b: UnicodeString(1, 10) }, false).domain;

    // Cast to Domain<unknown> since we're comparing structs with different shapes
    // (this is valid for backwards-compatibility checking)
    expect(newSchemaOptional.encapsulates(oldSchema as unknown as typeof newSchemaOptional).result).toBe('true');
    expect(newSchemaRequired.encapsulates(oldSchema as unknown as typeof newSchemaRequired).result).toBe('false');
  });

  it('works for STRING_DOMAIN with charset constraints', () => {
    const a = digits(1, 2).domain;
    const b = alphanumeric(1, 2).domain;
    const c = digits(2, 3).domain;

    expect(b.encapsulates(a).result).toBe('true');
    expect(b.encapsulates(c).result).toBe('false'); // length bounds narrower in b for c
  });

  it('works for STRING_DOMAIN compound parts (structural)', () => {
    const a = CompoundString('(', digits(3), ')').domain;
    const b = CompoundString('(', digits(3), ')').domain;
    const c = CompoundString('[', digits(3), ']').domain;

    expect(b.encapsulates(a).result).toBe('true');
    expect(b.encapsulates(c).result).toBe('false');
  });

  it('REGEX_DOMAIN: structural AST comparison for encapsulation', () => {
    const a = Regex(/^[a-z]+$/).domain;  // 1+ lowercase letters
    const b = Regex(/^[a-z]+$/).domain;  // same pattern
    const c = Regex(/^[a-z]{2,}$/).domain;  // 2+ lowercase letters

    // Equal patterns: true
    expect(b.encapsulates(a).result).toBe('true');
    
    // c does NOT encapsulate a because a accepts single letters but c requires 2+
    expect(c.encapsulates(a).result).toBe('false');
    
    // a DOES encapsulate c because every 2+ letter string is also a 1+ letter string
    expect(a.encapsulates(c).result).toBe('true');
  });
});


