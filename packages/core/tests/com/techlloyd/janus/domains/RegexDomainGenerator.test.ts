import { RegexDomainGenerator } from '@/com/techlloyd/janus/domains/RegexDomainGenerator';
import { DomainType, type RegexDomain } from '@/com/techlloyd/janus/Domain';
import { rngFromSequence } from './helpers';

describe('RegexDomainGenerator', () => {
  it('should generate a string that matches the regex source', () => {
    const generator = new RegexDomainGenerator();
    const domain: RegexDomain = {
      type: DomainType.REGEX_DOMAIN,
      source: 'a|b',
      pattern: /a|b/,
    };

    const value = generator.generate(domain, rngFromSequence([0.0]));
    expect(domain.pattern.test(value)).toBe(true);
  });

  it('should be influenced by RNG for alternations', () => {
    const generator = new RegexDomainGenerator();
    const domain: RegexDomain = {
      type: DomainType.REGEX_DOMAIN,
      source: 'a|b',
      pattern: /a|b/,
    };

    const a = generator.generate(domain, rngFromSequence([0.0]));
    const b = generator.generate(domain, rngFromSequence([0.99]));

    expect(a).toBe('a');
    expect(b).toBe('b');
  });
});


