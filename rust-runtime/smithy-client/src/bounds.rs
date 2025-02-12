//! This module holds convenient short-hands for the otherwise fairly extensive trait bounds
//! required for `call` and friends.
//!
//! The short-hands will one day be true [trait aliases], but for now they are traits with blanket
//! implementations. Also, due to [compiler limitations], the bounds repeat a nubmer of associated
//! types with bounds so that those bounds [do not need to be repeated] at the call site. It's a
//! bit of a mess to define, but _should_ be invisible to callers.
//!
//! [trait aliases]: https://rust-lang.github.io/rfcs/1733-trait-alias.html
//! [compiler limitations]: https://github.com/rust-lang/rust/issues/20671
//! [do not need to be repeated]: https://github.com/rust-lang/rust/issues/20671#issuecomment-529752828

use crate::*;

/// A service that has parsed a raw Smithy response.
pub type Parsed<S, O, Retry> = smithy_http_tower::parse_response::ParseResponseService<S, O, Retry>;

/// A low-level Smithy connector that maps from [`http::Request`] to [`http::Response`].
///
/// This trait has a blanket implementation for all compatible types, and should never be
/// implemented.
pub trait SmithyConnector:
    Service<
        http::Request<SdkBody>,
        Response = http::Response<SdkBody>,
        Error = <Self as SmithyConnector>::Error,
        Future = <Self as SmithyConnector>::Future,
    > + Send
    + Sync
    + Clone
    + 'static
{
    /// Forwarding type to `<Self as Service>::Error` for bound inference.
    ///
    /// See module-level docs for details.
    type Error: Into<BoxError> + Send + Sync + 'static;

    /// Forwarding type to `<Self as Service>::Future` for bound inference.
    ///
    /// See module-level docs for details.
    type Future: Send + 'static;
}

impl<T> SmithyConnector for T
where
    T: Service<http::Request<SdkBody>, Response = http::Response<SdkBody>>
        + Send
        + Sync
        + Clone
        + 'static,
    T::Error: Into<BoxError> + Send + Sync + 'static,
    T::Future: Send + 'static,
{
    type Error = T::Error;
    type Future = T::Future;
}

/// A Smithy middleware service that adjusts [`smithy_http::operation::Request`]s.
///
/// This trait has a blanket implementation for all compatible types, and should never be
/// implemented.
pub trait SmithyMiddlewareService:
    Service<
    smithy_http::operation::Request,
    Response = smithy_http::operation::Response,
    Error = smithy_http_tower::SendOperationError,
    Future = <Self as SmithyMiddlewareService>::Future,
>
{
    /// Forwarding type to `<Self as Service>::Future` for bound inference.
    ///
    /// See module-level docs for details.
    type Future: Send + 'static;
}

impl<T> SmithyMiddlewareService for T
where
    T: Service<
        smithy_http::operation::Request,
        Response = smithy_http::operation::Response,
        Error = smithy_http_tower::SendOperationError,
    >,
    T::Future: Send + 'static,
{
    type Future = T::Future;
}

/// A Smithy middleware layer (i.e., factory).
///
/// This trait has a blanket implementation for all compatible types, and should never be
/// implemented.
pub trait SmithyMiddleware<C>:
    Layer<
    smithy_http_tower::dispatch::DispatchService<C>,
    Service = <Self as SmithyMiddleware<C>>::Service,
>
{
    /// Forwarding type to `<Self as Layer>::Service` for bound inference.
    ///
    /// See module-level docs for details.
    type Service: SmithyMiddlewareService + Send + Sync + Clone + 'static;
}

impl<T, C> SmithyMiddleware<C> for T
where
    T: Layer<smithy_http_tower::dispatch::DispatchService<C>>,
    T::Service: SmithyMiddlewareService + Send + Sync + Clone + 'static,
{
    type Service = T::Service;
}

/// A Smithy retry policy.
///
/// This trait has a blanket implementation for all compatible types, and should never be
/// implemented.
pub trait SmithyRetryPolicy<O, T, E, Retry>:
    tower::retry::Policy<Operation<O, Retry>, SdkSuccess<T>, SdkError<E>> + Clone
{
    /// Forwarding type to `O` for bound inference.
    ///
    /// See module-level docs for details.
    type O: ParseHttpResponse<Output = Result<T, Self::E>> + Send + Sync + Clone + 'static;
    /// Forwarding type to `E` for bound inference.
    ///
    /// See module-level docs for details.
    type E: Error;

    /// Forwarding type to `Retry` for bound inference.
    ///
    /// See module-level docs for details.
    type Retry: ClassifyResponse<SdkSuccess<T>, SdkError<Self::E>>;
}

impl<R, O, T, E, Retry> SmithyRetryPolicy<O, T, E, Retry> for R
where
    R: tower::retry::Policy<Operation<O, Retry>, SdkSuccess<T>, SdkError<E>> + Clone,
    O: ParseHttpResponse<Output = Result<T, E>> + Send + Sync + Clone + 'static,
    E: Error,
    Retry: ClassifyResponse<SdkSuccess<T>, SdkError<E>>,
{
    type O = O;
    type E = E;
    type Retry = Retry;
}
