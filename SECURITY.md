# Security policy

## Reporting a vulnerability

Please report security problems privately through GitHub: open the repository's **Security** tab and choose **Report a vulnerability**, or go straight to <https://github.com/san-digital/det-prime/security/advisories/new>. Please do not open a public issue.

We will acknowledge your report and agree a disclosure date with you once a fix is ready.

## What counts

Examples of what we would treat as a security issue:

- `is_prime_u64`, or `is_prime` for `n < 2^64`, accepts a composite or rejects a prime.
- Any primality function rejects a prime.
- `sqrt_mod_prime` returns a wrong root for a prime modulus.
- A panic, hang, or arithmetic overflow on input the docs say is valid.

## Known limitations

These are documented behaviour, not vulnerabilities:

- The code is not constant-time. Do not use it on secret values.
- For `n >= 2^64`, rejecting every composite depends on the Generalized Riemann Hypothesis. See [`PROOF.md`](PROOF.md).

## Supported versions

Fixes go into the latest `0.1.x` release.
