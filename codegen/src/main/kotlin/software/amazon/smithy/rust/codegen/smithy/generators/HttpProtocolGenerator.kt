/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

package software.amazon.smithy.rust.codegen.smithy.generators

import software.amazon.smithy.aws.traits.ServiceTrait
import software.amazon.smithy.model.Model
import software.amazon.smithy.model.shapes.OperationShape
import software.amazon.smithy.model.shapes.ServiceShape
import software.amazon.smithy.model.shapes.ShapeId
import software.amazon.smithy.model.shapes.StructureShape
import software.amazon.smithy.rust.codegen.rustlang.Attribute
import software.amazon.smithy.rust.codegen.rustlang.CargoDependency
import software.amazon.smithy.rust.codegen.rustlang.RustWriter
import software.amazon.smithy.rust.codegen.rustlang.asType
import software.amazon.smithy.rust.codegen.rustlang.docs
import software.amazon.smithy.rust.codegen.rustlang.documentShape
import software.amazon.smithy.rust.codegen.rustlang.rust
import software.amazon.smithy.rust.codegen.rustlang.rustBlock
import software.amazon.smithy.rust.codegen.rustlang.rustBlockTemplate
import software.amazon.smithy.rust.codegen.rustlang.rustTemplate
import software.amazon.smithy.rust.codegen.rustlang.withBlock
import software.amazon.smithy.rust.codegen.smithy.RuntimeConfig
import software.amazon.smithy.rust.codegen.smithy.RuntimeType
import software.amazon.smithy.rust.codegen.smithy.RustSymbolProvider
import software.amazon.smithy.rust.codegen.smithy.customize.OperationCustomization
import software.amazon.smithy.rust.codegen.smithy.customize.OperationSection
import software.amazon.smithy.rust.codegen.smithy.customize.writeCustomizations
import software.amazon.smithy.rust.codegen.smithy.letIf
import software.amazon.smithy.rust.codegen.util.dq
import software.amazon.smithy.rust.codegen.util.getTrait
import software.amazon.smithy.rust.codegen.util.inputShape

/**
 * Configuration needed to generate the client for a given Service<->Protocol pair
 */
data class ProtocolConfig(
    val model: Model,
    val symbolProvider: RustSymbolProvider,
    val runtimeConfig: RuntimeConfig,
    val serviceShape: ServiceShape,
    val protocol: ShapeId,
    val moduleName: String
)

interface ProtocolGeneratorFactory<out T : HttpProtocolGenerator> {
    fun buildProtocolGenerator(protocolConfig: ProtocolConfig): T
    fun transformModel(model: Model): Model
    fun symbolProvider(model: Model, base: RustSymbolProvider): RustSymbolProvider = base
    fun support(): ProtocolSupport
}

/**
 * Abstract class providing scaffolding for HTTP based protocols that must build an HTTP request (headers / URL) and
 * a body.
 */
abstract class HttpProtocolGenerator(protocolConfig: ProtocolConfig) {
    private val runtimeConfig = protocolConfig.runtimeConfig
    private val symbolProvider = protocolConfig.symbolProvider
    private val model = protocolConfig.model

    private val sdkId =
        protocolConfig.serviceShape.getTrait<ServiceTrait>()?.sdkId?.toLowerCase()?.replace(" ", "")
            ?: protocolConfig.serviceShape.id.getName(protocolConfig.serviceShape)

    private val codegenScope = arrayOf(
        "HttpRequestBuilder" to RuntimeType.HttpRequestBuilder,
        "OpBuildError" to protocolConfig.runtimeConfig.operationBuildError(),
        "Request" to RuntimeType.Http("request::Request"),
        "RequestBuilder" to RuntimeType.HttpRequestBuilder,
        "SdkBody" to RuntimeType.sdkBody(protocolConfig.runtimeConfig),
        "config" to RuntimeType.Config,
        "header_util" to CargoDependency.SmithyHttp(protocolConfig.runtimeConfig).asType().member("header"),
        "http" to RuntimeType.http,
        "operation" to RuntimeType.operationModule(runtimeConfig),
    )

    data class BodyMetadata(val takesOwnership: Boolean)

    abstract fun RustWriter.body(self: String, operationShape: OperationShape): BodyMetadata

    abstract fun traitImplementations(operationWriter: RustWriter, operationShape: OperationShape)

    /** Write code into the impl block for [operationShape] */
    open fun operationImplBlock(implBlockWriter: RustWriter, operationShape: OperationShape) {}

    /**
     * Add necessary methods to the impl block for the input shape.
     *
     * Your implementation MUST call [generateRequestBuilderBase] to create the public method.
     */
    abstract fun toHttpRequestImpl(
        implBlockWriter: RustWriter,
        operationShape: OperationShape,
        inputShape: StructureShape
    )

    fun renderOperation(
        operationWriter: RustWriter,
        inputWriter: RustWriter,
        operationShape: OperationShape,
        customizations: List<OperationCustomization>
    ) {
        val inputShape = operationShape.inputShape(model)
        val builderGenerator = BuilderGenerator(model, symbolProvider, operationShape.inputShape(model))
        builderGenerator.render(inputWriter)

        // TODO: One day, it should be possible for callers to invoke
        // buildOperationType* directly to get the type rather than depending
        // on these aliases.
        val operationTypeOutput = buildOperationTypeOutput(inputWriter, operationShape)
        val operationTypeRetry = buildOperationTypeRetry(inputWriter, customizations)
        val inputPrefix = symbolProvider.toSymbol(inputShape).name
        inputWriter.rust(
            """
            ##[doc(hidden)] pub type ${inputPrefix}OperationOutputAlias = $operationTypeOutput;
            ##[doc(hidden)] pub type ${inputPrefix}OperationRetryAlias = $operationTypeRetry;
            """
        )

        // impl OperationInputShape { ... }
        val operationName = symbolProvider.toSymbol(operationShape).name
        inputWriter.implBlock(inputShape, symbolProvider) {
            writeCustomizations(customizations, OperationSection.InputImpl(operationShape, inputShape))
            generateMakeOperation(this, operationShape, operationName, customizations)
            toHttpRequestImpl(this, operationShape, inputShape)
            rustBlockTemplate(
                "fn assemble(mut builder: #{RequestBuilder}, body: #{SdkBody}) -> #{Request}<#{SdkBody}>",
                *codegenScope
            ) {
                rustTemplate(
                    """
                    if let Some(content_length) = body.content_length() {
                        builder = #{header_util}::set_header_if_absent(
                                    builder,
                                    #{http}::header::CONTENT_LENGTH,
                                    content_length
                        );
                    }
                    builder.body(body).expect("should be valid request")
                    """,
                    *codegenScope
                )
            }

            // pub fn builder() -> ... { }
            builderGenerator.renderConvenienceMethod(this)
        }

        // pub struct Operation { ... }
        operationWriter.documentShape(operationShape, model)
        Attribute.Derives(setOf(RuntimeType.Clone, RuntimeType.Default, RuntimeType.Debug)).render(operationWriter)
        operationWriter.rustBlock("pub struct $operationName") {
            write("_private: ()")
        }
        operationWriter.implBlock(operationShape, symbolProvider) {
            builderGenerator.renderConvenienceMethod(this)

            operationImplBlock(this, operationShape)

            rustBlock("pub fn new() -> Self") {
                rust("Self { _private: () }")
            }

            writeCustomizations(customizations, OperationSection.OperationImplBlock)
        }
        traitImplementations(operationWriter, operationShape)
    }

    protected fun generateRequestBuilderBase(implBlockWriter: RustWriter, f: RustWriter.() -> Unit) {
        Attribute.Custom("allow(clippy::unnecessary_wraps)").render(implBlockWriter)
        implBlockWriter.rustBlockTemplate(
            "fn request_builder_base(&self) -> std::result::Result<#{HttpRequestBuilder}, #{OpBuildError}>",
            *codegenScope,
        ) {
            f(this)
        }
    }

    private fun buildOperationType(
        writer: RustWriter,
        shape: OperationShape,
        customizations: List<OperationCustomization>,
    ): String {
        val operationT = RuntimeType.operation(runtimeConfig)
        val output = buildOperationTypeOutput(writer, shape)
        val retry = buildOperationTypeRetry(writer, customizations)

        return with(writer) { "${format(operationT)}<$output, $retry>" }
    }

    private fun buildOperationTypeOutput(writer: RustWriter, shape: OperationShape): String =
        writer.format(symbolProvider.toSymbol(shape))

    private fun buildOperationTypeRetry(writer: RustWriter, customizations: List<OperationCustomization>): String =
        customizations.mapNotNull { it.retryType() }.firstOrNull()?.let { writer.format(it) } ?: "()"

    private fun generateMakeOperation(
        implBlockWriter: RustWriter,
        shape: OperationShape,
        operationName: String,
        customizations: List<OperationCustomization>
    ) {
        val baseReturnType = buildOperationType(implBlockWriter, shape, customizations)
        val returnType = "std::result::Result<$baseReturnType, ${implBlockWriter.format(runtimeConfig.operationBuildError())}>"
        val outputSymbol = symbolProvider.toSymbol(shape)

        val bodyMetadata = RustWriter.root().body("self", shape)
        val mut = customizations.any { it.mutSelf() }
        val consumes = customizations.any { it.consumesSelf() } || bodyMetadata.takesOwnership
        val self = "self".letIf(mut) { "mut $it" }.letIf(!consumes) { "&$it" }

        implBlockWriter.docs("Consumes the builder and constructs an Operation<#D>", outputSymbol)
        implBlockWriter.rust("##[allow(clippy::let_and_return)]") // For codegen simplicity, allow `let x = ...; x`
        implBlockWriter.rustBlockTemplate(
            "pub fn make_operation($self, _config: &#{config}::Config) -> $returnType",
            *codegenScope
        ) {
            writeCustomizations(customizations, OperationSection.MutateInput("self", "_config"))
            rust("let properties = smithy_http::property_bag::SharedPropertyBag::new();")
            rust("let request = self.request_builder_base()?;")
            withBlock("let body =", ";") {
                body("self", shape)
            }
            rust("let request = Self::assemble(request, body);")
            rustTemplate(
                """
                ##[allow(unused_mut)]
                let mut request = #{operation}::Request::from_parts(request.map(#{SdkBody}::from), properties);
                """,
                *codegenScope
            )
            writeCustomizations(customizations, OperationSection.MutateRequest("request", "_config"))
            rustTemplate(
                """
                let op = #{operation}::Operation::new(request, #{OperationType}::new())
                    .with_metadata(#{operation}::Metadata::new(${operationName.dq()}, ${sdkId.dq()}));
                """,
                *codegenScope,
                "OperationType" to symbolProvider.toSymbol(shape)
            )
            writeCustomizations(customizations, OperationSection.FinalizeOperation("op", "_config"))
            rust("Ok(op)")
        }
    }
}
