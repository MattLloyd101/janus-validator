import {
  CharRange,
  normalizeRanges,
  rangesSize,
  rangesSubset,
  charsToRanges,
  charRange,
} from '@/com/techlloyd/janus/domains/CharRange';

describe('CharRange utilities', () => {
  describe('charRange', () => {
    it('creates a range from two characters', () => {
      const range = charRange('a', 'z');
      expect(range.min).toBe(97); // 'a'.codePointAt(0)
      expect(range.max).toBe(122); // 'z'.codePointAt(0)
    });

    it('handles single character range', () => {
      const range = charRange('x', 'x');
      expect(range.min).toBe(range.max);
    });

    it('handles Unicode characters', () => {
      const range = charRange('α', 'ω'); // Greek letters
      expect(range.min).toBe(945); // α
      expect(range.max).toBe(969); // ω
    });
  });

  describe('normalizeRanges', () => {
    it('returns empty array for empty input', () => {
      expect(normalizeRanges([])).toEqual([]);
    });

    it('returns single range unchanged', () => {
      const input: CharRange[] = [{ min: 10, max: 20 }];
      expect(normalizeRanges(input)).toEqual([{ min: 10, max: 20 }]);
    });

    it('merges overlapping ranges', () => {
      const input: CharRange[] = [
        { min: 0, max: 5 },
        { min: 3, max: 10 },
      ];
      expect(normalizeRanges(input)).toEqual([{ min: 0, max: 10 }]);
    });

    it('merges adjacent ranges', () => {
      const input: CharRange[] = [
        { min: 0, max: 5 },
        { min: 6, max: 10 },
      ];
      expect(normalizeRanges(input)).toEqual([{ min: 0, max: 10 }]);
    });

    it('keeps non-overlapping ranges separate', () => {
      const input: CharRange[] = [
        { min: 0, max: 5 },
        { min: 10, max: 15 },
      ];
      expect(normalizeRanges(input)).toEqual([
        { min: 0, max: 5 },
        { min: 10, max: 15 },
      ]);
    });

    it('sorts ranges by min value', () => {
      const input: CharRange[] = [
        { min: 20, max: 25 },
        { min: 0, max: 5 },
        { min: 10, max: 15 },
      ];
      const result = normalizeRanges(input);
      expect(result[0].min).toBeLessThan(result[1].min);
      expect(result[1].min).toBeLessThan(result[2].min);
    });

    it('handles fully contained ranges', () => {
      const input: CharRange[] = [
        { min: 0, max: 100 },
        { min: 20, max: 30 },
        { min: 50, max: 60 },
      ];
      expect(normalizeRanges(input)).toEqual([{ min: 0, max: 100 }]);
    });

    it('handles multiple overlapping ranges', () => {
      const input: CharRange[] = [
        { min: 0, max: 10 },
        { min: 5, max: 20 },
        { min: 15, max: 30 },
      ];
      expect(normalizeRanges(input)).toEqual([{ min: 0, max: 30 }]);
    });
  });

  describe('rangesSize', () => {
    it('returns 0 for empty array', () => {
      expect(rangesSize([])).toBe(0);
    });

    it('calculates size of single range', () => {
      expect(rangesSize([{ min: 0, max: 9 }])).toBe(10);
    });

    it('calculates size of single point range', () => {
      expect(rangesSize([{ min: 5, max: 5 }])).toBe(1);
    });

    it('sums sizes of multiple ranges', () => {
      const ranges: CharRange[] = [
        { min: 0, max: 9 },   // 10 chars
        { min: 20, max: 24 }, // 5 chars
      ];
      expect(rangesSize(ranges)).toBe(15);
    });
  });

  describe('rangesSubset', () => {
    it('empty inner is always subset', () => {
      expect(rangesSubset([{ min: 0, max: 10 }], [])).toBe(true);
    });

    it('any inner with empty outer is not subset', () => {
      expect(rangesSubset([], [{ min: 0, max: 10 }])).toBe(false);
    });

    it('returns true when inner is fully contained', () => {
      const outer: CharRange[] = [{ min: 0, max: 100 }];
      const inner: CharRange[] = [{ min: 10, max: 20 }];
      expect(rangesSubset(outer, inner)).toBe(true);
    });

    it('returns false when inner exceeds outer', () => {
      const outer: CharRange[] = [{ min: 10, max: 20 }];
      const inner: CharRange[] = [{ min: 5, max: 25 }];
      expect(rangesSubset(outer, inner)).toBe(false);
    });

    it('returns true for equal ranges', () => {
      const ranges: CharRange[] = [{ min: 10, max: 20 }];
      expect(rangesSubset(ranges, ranges)).toBe(true);
    });

    it('handles multiple outer ranges covering inner', () => {
      const outer: CharRange[] = [
        { min: 0, max: 10 },
        { min: 20, max: 30 },
      ];
      const inner: CharRange[] = [
        { min: 5, max: 8 },
        { min: 22, max: 25 },
      ];
      expect(rangesSubset(outer, inner)).toBe(true);
    });

    it('returns false when inner spans gap in outer', () => {
      const outer: CharRange[] = [
        { min: 0, max: 10 },
        { min: 20, max: 30 },
      ];
      const inner: CharRange[] = [{ min: 5, max: 25 }]; // spans the gap
      expect(rangesSubset(outer, inner)).toBe(false);
    });
  });

  describe('charsToRanges', () => {
    it('converts empty string to empty array', () => {
      expect(charsToRanges('')).toEqual([]);
    });

    it('converts single char to single point range', () => {
      const result = charsToRanges('a');
      expect(result).toEqual([{ min: 97, max: 97 }]);
    });

    it('merges consecutive characters into range', () => {
      const result = charsToRanges('abc');
      expect(result).toEqual([{ min: 97, max: 99 }]); // a-c
    });

    it('keeps non-consecutive characters separate', () => {
      const result = charsToRanges('aez');
      expect(result.length).toBe(3);
    });

    it('handles digits', () => {
      const result = charsToRanges('0123456789');
      expect(result).toEqual([{ min: 48, max: 57 }]); // 0-9
    });

    it('normalizes unordered input', () => {
      const result = charsToRanges('cba');
      expect(result).toEqual([{ min: 97, max: 99 }]); // still a-c
    });
  });
});

