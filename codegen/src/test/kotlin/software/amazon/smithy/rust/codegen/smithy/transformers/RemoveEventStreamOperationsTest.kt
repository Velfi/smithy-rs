/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

package software.amazon.smithy.rust.codegen.smithy.transformers

import io.kotest.matchers.shouldBe
import io.kotest.matchers.shouldNotBe
import org.junit.jupiter.api.Test
import software.amazon.smithy.model.shapes.Shape
import software.amazon.smithy.model.shapes.ShapeId
import software.amazon.smithy.rust.codegen.smithy.CodegenConfig
import software.amazon.smithy.rust.codegen.smithy.RuntimeConfig
import software.amazon.smithy.rust.codegen.smithy.RustSettings
import software.amazon.smithy.rust.codegen.testutil.asSmithyModel
import java.util.Optional

internal class RemoveEventStreamOperationsTest {
    private val model = """
        namespace test
        operation EventStream {
            input: StreamingInput,
        }

        operation BlobStream{
            input: BlobInput
        }

        structure BlobInput {
            blob: StreamingBlob
        }

        @streaming
        blob StreamingBlob

        structure StreamingInput {
            payload: Event
        }

        @streaming
        union Event {
            s: Foo
        }

        structure Foo {}
    """.asSmithyModel()

    @Test
    fun `remove event stream ops from services that are not in the allow list`() {
        val transformed = RemoveEventStreamOperations.transform(
            model,
            RustSettings(
                service = ShapeId.from("notrelevant#notrelevant"),
                moduleName = "test-module",
                moduleVersion = "notrelevant",
                moduleAuthors = listOf("notrelevant"),
                runtimeConfig = RuntimeConfig(),
                codegenConfig = CodegenConfig(eventStreamAllowList = setOf("not-test-module")),
                license = null,
                model = model
            )
        )
        transformed.expectShape(ShapeId.from("test#BlobStream"))
        transformed.getShape(ShapeId.from("test#EventStream")) shouldBe Optional.empty()
    }

    @Test
    fun `keep event stream ops from services that are in the allow list`() {
        val transformed = RemoveEventStreamOperations.transform(
            model,
            RustSettings(
                service = ShapeId.from("notrelevant#notrelevant"),
                moduleName = "test-module",
                moduleVersion = "notrelevant",
                moduleAuthors = listOf("notrelevant"),
                runtimeConfig = RuntimeConfig(),
                codegenConfig = CodegenConfig(eventStreamAllowList = setOf("test-module")),
                license = null,
                model = model
            )
        )
        transformed.expectShape(ShapeId.from("test#BlobStream"))
        transformed.getShape(ShapeId.from("test#EventStream")) shouldNotBe Optional.empty<Shape>()
    }
}
