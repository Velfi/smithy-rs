/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

package software.amazon.smithy.rustsdk.customize.s3

import software.amazon.smithy.aws.traits.protocols.RestXmlTrait
import software.amazon.smithy.model.Model
import software.amazon.smithy.model.shapes.IntegerShape
import software.amazon.smithy.model.shapes.LongShape
import software.amazon.smithy.model.shapes.OperationShape
import software.amazon.smithy.model.shapes.ShapeId
import software.amazon.smithy.model.transform.ModelTransformer
import software.amazon.smithy.rust.codegen.rustlang.CargoDependency
import software.amazon.smithy.rust.codegen.rustlang.RustModule
import software.amazon.smithy.rust.codegen.rustlang.Writable
import software.amazon.smithy.rust.codegen.rustlang.asType
import software.amazon.smithy.rust.codegen.rustlang.rust
import software.amazon.smithy.rust.codegen.rustlang.rustBlockTemplate
import software.amazon.smithy.rust.codegen.rustlang.rustTemplate
import software.amazon.smithy.rust.codegen.rustlang.writable
import software.amazon.smithy.rust.codegen.smithy.RuntimeType
import software.amazon.smithy.rust.codegen.smithy.customize.RustCodegenDecorator
import software.amazon.smithy.rust.codegen.smithy.generators.LibRsCustomization
import software.amazon.smithy.rust.codegen.smithy.generators.LibRsSection
import software.amazon.smithy.rust.codegen.smithy.generators.ProtocolConfig
import software.amazon.smithy.rust.codegen.smithy.letIf
import software.amazon.smithy.rust.codegen.smithy.protocols.ProtocolMap
import software.amazon.smithy.rust.codegen.smithy.protocols.RestXml
import software.amazon.smithy.rust.codegen.smithy.protocols.RestXmlFactory
import software.amazon.smithy.rustsdk.AwsRuntimeType

/**
 * Top level decorator for S3
 * */
class S3Decorator : RustCodegenDecorator {
    override val name: String = "S3ExtendedError"
    override val order: Byte = 0

    private fun applies(serviceId: ShapeId) =
        serviceId == ShapeId.from("com.amazonaws.s3#AmazonS3")

    override fun protocols(serviceId: ShapeId, currentProtocols: ProtocolMap): ProtocolMap {
        return currentProtocols.letIf(applies(serviceId)) {
            it + mapOf(
                RestXmlTrait.ID to RestXmlFactory { protocolConfig ->
                    S3(protocolConfig)
                }
            )
        }
    }

    override fun libRsCustomizations(
        protocolConfig: ProtocolConfig,
        baseCustomizations: List<LibRsCustomization>
    ): List<LibRsCustomization> {
        return baseCustomizations.letIf(applies(protocolConfig.serviceShape.id)) {
            it + S3PubUse()
        }
    }

    // TODO: Uncomment once https://github.com/awslabs/smithy/pull/900 is merged and
    // the latest Smithy is pulled in.
    // override fun transformModel(service: ServiceShape, model: Model): Model =
    //     S3CorrectSizeIntegerType().transform(model)
}

class S3(protocolConfig: ProtocolConfig) : RestXml(protocolConfig) {
    private val runtimeConfig = protocolConfig.runtimeConfig
    private val errorScope = arrayOf(
        "Bytes" to RuntimeType.Bytes,
        "Error" to RuntimeType.GenericError(runtimeConfig),
        "HeaderMap" to RuntimeType.http.member("HeaderMap"),
        "Response" to RuntimeType.http.member("Response"),
        "XmlError" to CargoDependency.smithyXml(runtimeConfig).asType().member("decode::XmlError"),
        "base_errors" to restXmlErrors,
        "s3_errors" to AwsRuntimeType.S3Errors,
    )

    override fun parseHttpGenericError(operationShape: OperationShape): RuntimeType {
        return RuntimeType.forInlineFun("parse_http_generic_error", RustModule.private("xml_deser")) {
            it.rustBlockTemplate(
                "pub fn parse_http_generic_error(response: &#{Response}<#{Bytes}>) -> Result<#{Error}, #{XmlError}>",
                *errorScope
            ) {
                rustTemplate(
                    """
                    if response.body().is_empty() {
                        let mut err = #{Error}::builder();
                        if response.status().as_u16() == 404 {
                            err.code("NotFound");
                        }
                        Ok(err.build())
                    } else {
                        let base_err = #{base_errors}::parse_generic_error(response.body().as_ref())?;
                        Ok(#{s3_errors}::parse_extended_error(base_err, response.headers()))
                    }
                    """,
                    *errorScope
                )
            }
        }
    }
}

class S3PubUse : LibRsCustomization() {
    override fun section(section: LibRsSection): Writable = when (section) {
        is LibRsSection.Body -> writable { rust("pub use #T::ErrorExt;", AwsRuntimeType.S3Errors) }
        else -> emptySection
    }
}

/** `com.amazonaws.s3#Size` is modeled as `integer`, which is too small for file sizes */
class S3CorrectSizeIntegerType {
    companion object {
        val SIZE_SHAPE_ID = ShapeId.from("com.amazonaws.s3#Size")
    }

    fun transform(model: Model): Model = ModelTransformer.create().mapShapes(model) { shape ->
        if (shape is IntegerShape && shape.id == SIZE_SHAPE_ID) {
            LongShape.builder().id(shape.id).source(shape.sourceLocation).traits(shape.allTraits.values).build()
        } else {
            shape
        }
    }
}
