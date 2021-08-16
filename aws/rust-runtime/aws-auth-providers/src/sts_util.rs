/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

use aws_auth::provider::{CredentialsError, CredentialsResult};
use aws_auth::Credentials as AwsCredentials;
use aws_sdk_sts::model::Credentials as StsCredentials;
use std::time::{SystemTime, UNIX_EPOCH};

pub fn into_credentials(
    sts_credentials: Option<StsCredentials>,
    provider_name: &'static str,
) -> CredentialsResult {
    let sts_credentials = sts_credentials
        .ok_or_else(|| CredentialsError::Unhandled("STS credentials must be defined".into()))?;
    let expiration = sts_credentials
        .expiration
        .ok_or_else(|| CredentialsError::Unhandled("missing expiration".into()))?;
    let expiration = expiration.to_system_time().ok_or_else(|| {
        CredentialsError::Unhandled(
            format!("expiration is before unix epoch: {:?}", &expiration).into(),
        )
    })?;
    Ok(AwsCredentials::new(
        sts_credentials.access_key_id.ok_or_else(|| {
            CredentialsError::Unhandled("access key id missing from result".into())
        })?,
        sts_credentials
            .secret_access_key
            .ok_or_else(|| CredentialsError::Unhandled("secret access token missing".into()))?,
        sts_credentials.session_token,
        Some(expiration),
        provider_name,
    ))
}

pub fn default_session_name(base: &str) -> String {
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("post epoch");
    format!("{}-{}", base, now.as_millis())
}
