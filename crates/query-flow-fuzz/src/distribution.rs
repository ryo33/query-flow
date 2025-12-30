//! Probability distributions and scale utilities.

use rand::Rng;

/// Logarithmic scale for generating parameter values.
///
/// # Example
/// ```
/// use query_flow_fuzz::LogScale;
///
/// let scale = LogScale::new(10, 0, 3);
/// let values: Vec<_> = scale.values().collect();
/// assert_eq!(values, vec![1, 10, 100, 1000]);
/// ```
#[derive(Debug, Clone, Copy)]
pub struct LogScale {
    pub base: u32,
    pub min_exp: u32,
    pub max_exp: u32,
}

impl LogScale {
    pub const fn new(base: u32, min_exp: u32, max_exp: u32) -> Self {
        Self {
            base,
            min_exp,
            max_exp,
        }
    }

    /// Standard base-10 logarithmic scale: 1, 10, 100, 1000
    pub const STANDARD: Self = Self::new(10, 0, 3);

    /// Binary scale: 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024
    pub const BINARY: Self = Self::new(2, 0, 10);

    /// Small scale for quick tests: 1, 10, 100
    pub const SMALL: Self = Self::new(10, 0, 2);

    /// Returns an iterator over the scale values.
    pub fn values(&self) -> impl Iterator<Item = u64> {
        let base = self.base as u64;
        let min_exp = self.min_exp;
        let max_exp = self.max_exp;
        (min_exp..=max_exp).map(move |exp| base.pow(exp))
    }

    /// Returns the number of values in this scale.
    pub fn len(&self) -> usize {
        (self.max_exp - self.min_exp + 1) as usize
    }

    /// Returns true if the scale is empty.
    pub fn is_empty(&self) -> bool {
        self.min_exp > self.max_exp
    }
}

/// Distribution type for sampling values.
#[derive(Debug, Clone, Copy, PartialEq, Default)]
pub enum Distribution {
    /// Always returns the same value (min).
    #[default]
    Constant,
    /// Uniform distribution between min and max.
    Uniform,
    /// Normal distribution with mean at (min+max)/2.
    Normal {
        /// Standard deviation as a fraction of the range (0.0 to 1.0).
        stddev_fraction: f64,
    },
    /// Exponential distribution.
    Exponential {
        /// Lambda parameter (rate).
        lambda: f64,
    },
    /// Bimodal distribution: either fast or slow.
    Bimodal {
        /// Probability of the fast (min) value.
        fast_probability: f64,
    },
}

/// Sample a value from a distribution within a range.
pub fn sample_in_range<R: Rng>(rng: &mut R, min: u64, max: u64, distribution: Distribution) -> u64 {
    if min == max {
        return min;
    }

    match distribution {
        Distribution::Constant => min,
        Distribution::Uniform => rng.gen_range(min..=max),
        Distribution::Normal { stddev_fraction } => {
            let mean = (min + max) as f64 / 2.0;
            let stddev = (max - min) as f64 * stddev_fraction;
            let value = sample_normal(rng, mean, stddev);
            value.clamp(min as f64, max as f64) as u64
        }
        Distribution::Exponential { lambda } => {
            let value = sample_exponential(rng, lambda);
            (min as f64 + value).min(max as f64) as u64
        }
        Distribution::Bimodal { fast_probability } => {
            if rng.gen::<f64>() < fast_probability {
                min
            } else {
                max
            }
        }
    }
}

/// Sample from a normal distribution using Box-Muller transform.
fn sample_normal<R: Rng>(rng: &mut R, mean: f64, stddev: f64) -> f64 {
    let u1: f64 = rng.gen();
    let u2: f64 = rng.gen();
    let z = (-2.0 * u1.ln()).sqrt() * (2.0 * std::f64::consts::PI * u2).cos();
    mean + z * stddev
}

/// Sample from an exponential distribution.
fn sample_exponential<R: Rng>(rng: &mut R, lambda: f64) -> f64 {
    let u: f64 = rng.gen();
    -u.ln() / lambda
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_log_scale_standard() {
        let values: Vec<_> = LogScale::STANDARD.values().collect();
        assert_eq!(values, vec![1, 10, 100, 1000]);
    }

    #[test]
    fn test_log_scale_binary() {
        let values: Vec<_> = LogScale::new(2, 0, 4).values().collect();
        assert_eq!(values, vec![1, 2, 4, 8, 16]);
    }

    #[test]
    fn test_log_scale_len() {
        assert_eq!(LogScale::STANDARD.len(), 4);
        assert_eq!(LogScale::SMALL.len(), 3);
    }

    #[test]
    fn test_sample_constant() {
        let mut rng = rand::thread_rng();
        for _ in 0..10 {
            assert_eq!(
                sample_in_range(&mut rng, 42, 100, Distribution::Constant),
                42
            );
        }
    }

    #[test]
    fn test_sample_uniform() {
        let mut rng = rand::thread_rng();
        for _ in 0..100 {
            let value = sample_in_range(&mut rng, 10, 20, Distribution::Uniform);
            assert!((10..=20).contains(&value));
        }
    }

    #[test]
    fn test_sample_bimodal() {
        let mut rng = rand::thread_rng();
        let mut min_count = 0;
        let mut max_count = 0;
        for _ in 0..1000 {
            let value = sample_in_range(
                &mut rng,
                0,
                100,
                Distribution::Bimodal {
                    fast_probability: 0.5,
                },
            );
            if value == 0 {
                min_count += 1;
            } else if value == 100 {
                max_count += 1;
            }
        }
        // Both should be roughly 500, allow for variance
        assert!(min_count > 400 && min_count < 600);
        assert!(max_count > 400 && max_count < 600);
    }
}
