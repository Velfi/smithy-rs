/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

//! This module defines types that describe when to retry given a response.

use std::{default::Default, time::Duration};

#[derive(Clone, Copy, Eq, PartialEq, Debug)]
#[non_exhaustive]
pub enum ErrorKind {
    /// A connection-level error.
    ///
    /// A `TransientError` can represent conditions such as socket timeouts, socket connection errors, or TLS negotiation timeouts.
    ///
    /// `TransientError` is not modeled by Smithy and is instead determined through client-specific heuristics and response status codes.
    ///
    /// Typically these should never be applied for non-idempotent request types
    /// since in this scenario, it's impossible to know whether the operation had
    /// a side effect on the server.
    ///
    /// TransientErrors are not currently modeled. They are determined based on specific provider
    /// level errors & response status code.
    TransientError,

    /// An error where the server explicitly told the client to back off, such as a 429 or 503 HTTP error.
    ThrottlingError,

    /// Server error that isn't explicitly throttling but is considered by the client
    /// to be something that should be retried.
    ServerError,

    /// Doesn't count against any budgets. This could be something like a 401 challenge in Http.
    ClientError,
}

pub trait ProvideErrorKind {
    /// Returns the `ErrorKind` when the error is modeled as retryable
    ///
    /// If the error kind cannot be determined (eg. the error is unmodeled at the error kind depends
    /// on an HTTP status code, return `None`.
    fn retryable_error_kind(&self) -> Option<ErrorKind>;

    /// Returns the `code` for this error if one exists
    fn code(&self) -> Option<&str>;
}

/// `RetryKind` describes how a request MAY be retried for a given response
///
/// A `RetryKind` describes how a response MAY be retried; it does not mandate retry behavior.
/// The actual retry behavior is at the sole discretion of the RetryStrategy in place.
/// A RetryStrategy may ignore the suggestion for a number of reasons including but not limited to:
/// - Number of retry attempts exceeded
/// - The required retry delay exceeds the maximum backoff configured by the client
/// - No retry tokens are available due to service health
#[non_exhaustive]
#[derive(Eq, PartialEq, Debug)]
pub enum RetryKind {
    /// Retry the associated request due to a known `ErrorKind`.
    Error(ErrorKind),

    /// An Explicit retry (eg. from `x-amz-retry-after`).
    ///
    /// Note: The specified `Duration` is considered a suggestion and may be replaced or ignored.
    Explicit(Duration),

    /// The response associated with this variant should not be retried.
    NotRetryable,
}

#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RetryMode {
    /// The default retry behavior used by SDK clients, rate-limited with a configurable number of max attempts.
    Standard,
    /// This behavior includes the functionality of standard mode but with automatic client-side throttling. Currently unimplemented
    Adaptive,
}

impl Default for RetryMode {
    fn default() -> Self {
        RetryMode::Standard
    }
}

/// Retry Policy Configuration
///
/// Without specific use cases, users should generally rely on the default values set by `[Config::default]`(Config::default).`
///
/// Currently these fields are private and no setters provided. As needed, this configuration will become user-modifiable in the future..
#[derive(Clone, Debug)]
pub struct RetryConfig {
    base_fn: fn() -> f64,
    initial_retry_tokens: usize,
    max_attempts: u32,
    max_backoff: Duration,
    mode: RetryMode,
    no_retry_increment: usize,
    retry_cost: usize,
    timeout_retry_cost: usize,
}

impl RetryConfig {
    pub fn new() -> Self {
        Default::default()
    }

    /// Override `b` in the exponential backoff computation
    ///
    /// By default, `base` is a randomly generated value between 0 and 1. In tests, it can
    /// be helpful to override this:
    /// ```rust
    /// use smithy_client::retry::Config;
    /// let conf = Config::default().with_base(||1_f64);
    /// ```
    pub fn with_base(mut self, base: fn() -> f64) -> Self {
        self.base_fn = base;
        self
    }

    /// Override the retry mode
    pub fn with_mode(mut self, mode: RetryMode) -> Self {
        self.mode = mode;
        self
    }

    /// Override the maximum number of attempts
    pub fn with_max_attempts(mut self, max_attempts: u32) -> Self {
        self.max_attempts = max_attempts;
        self
    }

    /// Override the initial amount of retry tokens
    pub fn with_initial_retry_tokens(mut self, initial_retry_tokens: usize) -> Self {
        self.initial_retry_tokens = initial_retry_tokens;
        self
    }

    /// Override the maximum retry backoff
    pub fn with_max_backoff(mut self, max_backoff: Duration) -> Self {
        self.max_backoff = max_backoff;
        self
    }

    /// Get the retry config's max attempts.
    pub fn max_attempts(&self) -> u32 {
        self.max_attempts
    }

    /// Get the retry config's max backoff.
    pub fn max_backoff(&self) -> Duration {
        self.max_backoff
    }

    pub fn base(&self) -> f64 {
        (self.base_fn)()
    }

    /// Get the retry config's no retry increment.
    pub fn no_retry_increment(&self) -> usize {
        self.no_retry_increment
    }

    /// Get the retry config's retry cost.
    pub fn retry_cost(&self) -> usize {
        self.retry_cost
    }

    /// Get the retry config's timeout retry cost.
    pub fn timeout_retry_cost(&self) -> usize {
        self.timeout_retry_cost
    }

    /// Get the retry config's initial retry tokens.
    pub fn initial_retry_tokens(&self) -> usize {
        self.initial_retry_tokens
    }

    /// Get the retry config's mode.
    pub fn mode(&self) -> RetryMode {
        self.mode
    }
}

const MAX_ATTEMPTS: u32 = 3;
const INITIAL_RETRY_TOKENS: usize = 500;
const RETRY_COST: usize = 5;

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            mode: Default::default(),
            initial_retry_tokens: INITIAL_RETRY_TOKENS,
            retry_cost: RETRY_COST,
            no_retry_increment: 1,
            timeout_retry_cost: 10,
            max_attempts: MAX_ATTEMPTS,
            max_backoff: Duration::from_secs(20),
            // by default, use a random base for exponential backoff
            base_fn: fastrand::f64,
        }
    }
}
