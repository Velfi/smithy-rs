/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

use aws_types::credentials::future;
use aws_types::credentials::{CredentialsError, ProvideCredentials};

/// Stub credentials provider for use when no credentials provider is used.
#[non_exhaustive]
#[derive(Debug)]
pub struct NoCredentials;

impl ProvideCredentials for NoCredentials {
    fn provide_credentials<'a>(&'a self) -> future::ProvideCredentials<'a>
    where
        Self: 'a,
    {
        future::ProvideCredentials::ready(Err(CredentialsError::CredentialsNotLoaded))
    }
}
