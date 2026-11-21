/// Maximum supported sieve limit (`16,500,000`), exceeding `2 * (ln(2^4096))^2` (`16,121,365`).
pub const MAX_SIEVE_LIMIT: u64 = 16_500_000;

const SEED_COUNT: usize = 559;

/// Compile-time table of the 559 odd primes from `3` through `4,057` (`4057^2 = 16,459,249`,
/// next prime `4073^2 = 16,589,329 > 16,500,000`).
const SEED_ODD_PRIMES: [u16; SEED_COUNT] = build_seed_primes();

const _: () = {
    assert!(SEED_ODD_PRIMES[SEED_COUNT - 1] == 4057);
    assert!(4073u64 * 4073u64 > MAX_SIEVE_LIMIT);
};

const fn build_seed_primes() -> [u16; SEED_COUNT] {
    let mut out = [0u16; SEED_COUNT];
    let mut count = 0usize;
    let mut cand = 3u32;
    while count < SEED_COUNT {
        let mut is_p = true;
        let mut i = 0usize;
        while i < count {
            let p = out[i] as u32;
            if p * p > cand {
                break;
            }
            if cand % p == 0 {
                is_p = false;
                break;
            }
            i += 1;
        }
        if is_p {
            out[count] = cand as u16;
            count += 1;
        }
        cand += 2;
    }
    out
}

/// Small odd primes for rapid composite pre-filtering before Montgomery setup.
pub const SMALL_ODD_PRIMES: &[u16] = &SEED_ODD_PRIMES;

const SEG_WORDS: usize = 64;
const SEG_ODDS: u64 = (SEG_WORDS as u64) * 64; // 4,096 odd integers = span of 8,192

/// Zero-allocation segmented prime iterator yielding all primes `2 <= p <= limit`
/// for any `limit <= MAX_SIEVE_LIMIT`.
pub struct PrimeIter {
    limit: u64,
    emitted_two: bool,
    seg_low_odd: u64,
    bits: [u64; SEG_WORDS], // 1 bit = composite
    word_idx: usize,
    cur_word: u64,
}

impl PrimeIter {
    /// Creates an iterator over all primes `<= limit` (clamped to `MAX_SIEVE_LIMIT`).
    pub fn up_to(limit: u64) -> Self {
        let capped = if limit > MAX_SIEVE_LIMIT {
            MAX_SIEVE_LIMIT
        } else {
            limit
        };
        let mut iter = Self {
            limit: capped,
            emitted_two: false,
            seg_low_odd: 3,
            bits: [0u64; SEG_WORDS],
            word_idx: SEG_WORDS,
            cur_word: 0,
        };
        if capped >= 3 {
            iter.refill_segment(3);
        }
        iter
    }

    fn refill_segment(&mut self, start_odd: u64) {
        self.seg_low_odd = start_odd;
        self.bits = [0u64; SEG_WORDS];
        let seg_high_odd = start_odd + 2 * (SEG_ODDS - 1);
        let bound = if seg_high_odd > self.limit {
            self.limit
        } else {
            seg_high_odd
        };

        for &p16 in &SEED_ODD_PRIMES {
            let p = p16 as u64;
            let p2 = p * p;
            if p2 > bound {
                break;
            }
            let mut first = if p2 >= start_odd {
                p2
            } else {
                let rem = start_odd % p;
                let mut m = if rem == 0 {
                    start_odd
                } else {
                    start_odd + (p - rem)
                };
                if (m & 1) == 0 {
                    m += p;
                }
                m
            };
            let step = 2 * p;
            while first <= bound {
                let idx = ((first - start_odd) / 2) as usize;
                self.bits[idx / 64] |= 1u64 << (idx % 64);
                first += step;
            }
        }
        self.word_idx = 0;
        self.cur_word = !self.bits[0];
    }
}

impl Iterator for PrimeIter {
    type Item = u64;

    fn next(&mut self) -> Option<u64> {
        if self.limit < 2 {
            return None;
        }
        if !self.emitted_two {
            self.emitted_two = true;
            return Some(2);
        }
        if self.limit < 3 {
            return None;
        }
        loop {
            if self.cur_word != 0 {
                let bit = self.cur_word.trailing_zeros() as u64;
                self.cur_word &= self.cur_word - 1;
                let idx = (self.word_idx as u64) * 64 + bit;
                let cand = self.seg_low_odd + 2 * idx;
                if cand <= self.limit {
                    return Some(cand);
                } else {
                    self.word_idx = SEG_WORDS;
                    self.cur_word = 0;
                    return None;
                }
            }
            self.word_idx += 1;
            if self.word_idx < SEG_WORDS {
                self.cur_word = !self.bits[self.word_idx];
            } else {
                let next_start = self.seg_low_odd + 2 * SEG_ODDS;
                if next_start > self.limit {
                    return None;
                }
                self.refill_segment(next_start);
            }
        }
    }
}
