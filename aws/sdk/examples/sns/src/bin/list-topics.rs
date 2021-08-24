/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

use aws_sdk_sns::{Client, Config, Error, Region, PKG_VERSION};
use aws_types::region;

use structopt::StructOpt;

#[derive(Debug, StructOpt)]
struct Opt {
    /// The AWS Region.
    #[structopt(short, long)]
    region: Option<String>,

    /// Whether to display additional information.
    #[structopt(short, long)]
    verbose: bool,
}

/// Lists your Amazon SNS topics in the region.
/// # Arguments
///
/// * `[-r REGION]` - The Region in which the client is created.
///    If not supplied, uses the value of the **AWS_REGION** environment variable.
///    If the environment variable is not set, defaults to **us-west-2**.
/// * `[-v]` - Whether to display additional information.
#[tokio::main]
async fn main() -> Result<(), Error> {
    tracing_subscriber::fmt::init();

    let Opt { region, verbose } = Opt::from_args();

    let region = region::ChainProvider::first_try(region.map(Region::new))
        .or_default_provider()
        .or_else(Region::new("us-west-2"));

    println!();

    if verbose {
        println!("SNS client version:   {}", PKG_VERSION);
        println!(
            "Region:               {}",
            region.region().await.unwrap().as_ref()
        );

        println!();
    }

    let conf = Config::builder().region(region.region().await).build();
    let client = Client::from_conf(conf);

    let resp = client.list_topics().send().await?;

    println!("Topic ARNs:");

    for topic in resp.topics.unwrap_or_default() {
        println!("{}", topic.topic_arn.as_deref().unwrap_or_default());
    }
    Ok(())
}
