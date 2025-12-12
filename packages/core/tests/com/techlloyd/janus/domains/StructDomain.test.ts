import {
  StructDomain,
  FiniteDomain,
  ContiguousDomain,
  ContiguousType,
  AlternationDomain,
} from '@/com/techlloyd/janus/Domain';
import { DomainType } from '@/com/techlloyd/janus/domains/types';

describe('StructDomain', () => {
  describe('construction', () => {
    it('creates domain with schema', () => {
      const schema = {
        name: new FiniteDomain(['Alice', 'Bob']),
        age: new ContiguousDomain(ContiguousType.INTEGER, 0, 150),
      };
      const domain = new StructDomain(schema, false);
      expect(domain.type).toBe(DomainType.STRUCT_DOMAIN);
      expect(domain.schema).toBe(schema);
      expect(domain.strict).toBe(false);
    });

    it('supports strict mode', () => {
      const domain = new StructDomain({}, true);
      expect(domain.strict).toBe(true);
    });

    it('supports non-strict mode', () => {
      const domain = new StructDomain({}, false);
      expect(domain.strict).toBe(false);
    });
  });

  describe('encapsulates', () => {
    describe('field compatibility', () => {
      it('encapsulates when all fields encapsulate', () => {
        const wide = new StructDomain({
          x: new ContiguousDomain(ContiguousType.INTEGER, 0, 100),
          y: new ContiguousDomain(ContiguousType.INTEGER, 0, 100),
        }, false);
        const narrow = new StructDomain({
          x: new ContiguousDomain(ContiguousType.INTEGER, 10, 50),
          y: new ContiguousDomain(ContiguousType.INTEGER, 20, 60),
        }, false);

        expect(wide.encapsulates(narrow).result).toBe('true');
      });

      it('does not encapsulate when any field fails', () => {
        const dom1 = new StructDomain({
          x: new ContiguousDomain(ContiguousType.INTEGER, 0, 50),
          y: new ContiguousDomain(ContiguousType.INTEGER, 0, 100),
        }, false);
        const dom2 = new StructDomain({
          x: new ContiguousDomain(ContiguousType.INTEGER, 0, 100), // exceeds
          y: new ContiguousDomain(ContiguousType.INTEGER, 0, 50),
        }, false);

        expect(dom1.encapsulates(dom2).result).toBe('false');
      });

      it('handles nested structs', () => {
        const wide = new StructDomain({
          nested: new StructDomain({
            value: new ContiguousDomain(ContiguousType.INTEGER, 0, 100),
          }, false),
        }, false);
        const narrow = new StructDomain({
          nested: new StructDomain({
            value: new ContiguousDomain(ContiguousType.INTEGER, 10, 50),
          }, false),
        }, false);

        expect(wide.encapsulates(narrow).result).toBe('true');
      });
    });

    describe('strictness compatibility', () => {
      it('non-strict encapsulates non-strict', () => {
        const a = new StructDomain({ x: new FiniteDomain([1]) }, false);
        const b = new StructDomain({ x: new FiniteDomain([1]) }, false);
        expect(a.encapsulates(b).result).toBe('true');
      });

      it('strict encapsulates strict', () => {
        const a = new StructDomain({ x: new FiniteDomain([1]) }, true);
        const b = new StructDomain({ x: new FiniteDomain([1]) }, true);
        expect(a.encapsulates(b).result).toBe('true');
      });

      it('non-strict encapsulates strict', () => {
        const nonStrict = new StructDomain({ x: new FiniteDomain([1]) }, false);
        const strict = new StructDomain({ x: new FiniteDomain([1]) }, true);
        expect(nonStrict.encapsulates(strict).result).toBe('true');
      });

      it('strict does not encapsulate non-strict (tightening)', () => {
        const strict = new StructDomain({ x: new FiniteDomain([1]) }, true);
        const nonStrict = new StructDomain({ x: new FiniteDomain([1]) }, false);
        expect(strict.encapsulates(nonStrict).result).toBe('false');
      });
    });

    describe('field addition/removal', () => {
      it('adding optional field (accepts undefined) is compatible', () => {
        const oldSchema = new StructDomain({
          x: new ContiguousDomain(ContiguousType.INTEGER, 0, 100),
        }, false);
        const newSchema = new StructDomain({
          x: new ContiguousDomain(ContiguousType.INTEGER, 0, 100),
          y: new AlternationDomain([
            new FiniteDomain([undefined]),
            new ContiguousDomain(ContiguousType.INTEGER, 0, 50),
          ]),
        }, false);

        // Cast needed because schemas have different shapes
        expect(newSchema.encapsulates(oldSchema as any).result).toBe('true');
      });

      it('adding required field is not compatible', () => {
        const oldSchema = new StructDomain({
          x: new ContiguousDomain(ContiguousType.INTEGER, 0, 100),
        }, false);
        const newSchema = new StructDomain({
          x: new ContiguousDomain(ContiguousType.INTEGER, 0, 100),
          y: new ContiguousDomain(ContiguousType.INTEGER, 0, 50), // required
        }, false);

        expect(newSchema.encapsulates(oldSchema as any).result).toBe('false');
      });

      it('removing field (missing in new) fails if new is strict', () => {
        // This tests the scenario where old has more fields than new
        const withField = new StructDomain({
          x: new FiniteDomain([1]),
          y: new FiniteDomain([2]),
        }, false);
        const withoutField = new StructDomain({
          x: new FiniteDomain([1]),
        }, true); // strict - won't accept extra fields

        expect(withoutField.encapsulates(withField as any).result).toBe('false');
      });
    });

    describe('empty schemas', () => {
      it('empty schemas encapsulate each other', () => {
        const a = new StructDomain({}, false);
        const b = new StructDomain({}, false);
        expect(a.encapsulates(b).result).toBe('true');
        expect(b.encapsulates(a).result).toBe('true');
      });

      it('empty struct does not encapsulate non-empty (missing fields)', () => {
        const empty = new StructDomain({}, false);
        const nonEmpty = new StructDomain({
          x: new FiniteDomain([1]),
        }, false);
        // empty lacks field 'x' that nonEmpty has - cannot encapsulate
        expect(empty.encapsulates(nonEmpty as any).result).toBe('false');
      });

      it('non-empty encapsulates empty (no missing fields)', () => {
        const empty = new StructDomain({}, false);
        const nonEmpty = new StructDomain({
          x: new AlternationDomain([
            new FiniteDomain([undefined]),
            new FiniteDomain([1]),
          ]),
        }, false);
        // nonEmpty has all of empty's fields (none) plus optional field x
        expect(nonEmpty.encapsulates(empty as any).result).toBe('true');
      });
    });
  });
});
