/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

package software.amazon.smithy.rust.codegen.smithy.protocols.parse

import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.ArgumentsSource
import software.amazon.smithy.model.shapes.ShapeId
import software.amazon.smithy.rust.codegen.rustlang.rust
import software.amazon.smithy.rust.codegen.smithy.generators.ProtocolConfig
import software.amazon.smithy.rust.codegen.smithy.protocols.EventStreamTestModels
import software.amazon.smithy.rust.codegen.smithy.protocols.EventStreamTestTools
import software.amazon.smithy.rust.codegen.testutil.TestRuntimeConfig
import software.amazon.smithy.rust.codegen.testutil.compileAndTest
import software.amazon.smithy.rust.codegen.testutil.unitTest

class EventStreamUnmarshallerGeneratorTest {
    @ParameterizedTest
    @ArgumentsSource(EventStreamTestModels.UnmarshallTestCasesProvider::class)
    fun test(testCase: EventStreamTestModels.TestCase) {
        val test = EventStreamTestTools.generateTestProject(testCase.model)

        val protocolConfig = ProtocolConfig(
            test.model,
            test.symbolProvider,
            TestRuntimeConfig,
            test.serviceShape,
            ShapeId.from(testCase.protocolShapeId),
            "test"
        )
        val protocol = testCase.protocolBuilder(protocolConfig)
        val generator = EventStreamUnmarshallerGenerator(
            protocol,
            test.model,
            TestRuntimeConfig,
            test.symbolProvider,
            test.operationShape,
            test.streamShape
        )

        test.project.lib { writer ->
            writer.rust(
                """
                use smithy_eventstream::frame::{Header, HeaderValue, Message, UnmarshallMessage, UnmarshalledMessage};
                use smithy_types::{Blob, Instant};
                use crate::error::*;
                use crate::model::*;

                fn msg(
                    message_type: &'static str,
                    event_type: &'static str,
                    content_type: &'static str,
                    payload: &'static [u8],
                ) -> Message {
                    let message = Message::new(payload)
                        .add_header(Header::new(":message-type", HeaderValue::String(message_type.into())))
                        .add_header(Header::new(":content-type", HeaderValue::String(content_type.into())));
                    if message_type == "event" {
                        message.add_header(Header::new(":event-type", HeaderValue::String(event_type.into())))
                    } else {
                        message.add_header(Header::new(":exception-type", HeaderValue::String(event_type.into())))
                    }
                }
                fn expect_event<T: std::fmt::Debug, E: std::fmt::Debug>(unmarshalled: UnmarshalledMessage<T, E>) -> T {
                    match unmarshalled {
                        UnmarshalledMessage::Event(event) => event,
                        _ => panic!("expected event, got: {:?}", unmarshalled),
                    }
                }
                fn expect_error<T: std::fmt::Debug, E: std::fmt::Debug>(unmarshalled: UnmarshalledMessage<T, E>) -> E {
                    match unmarshalled {
                        UnmarshalledMessage::Error(error) => error,
                        _ => panic!("expected error, got: {:?}", unmarshalled),
                    }
                }
                """
            )

            writer.unitTest(
                """
                let message = msg("event", "MessageWithBlob", "application/octet-stream", b"hello, world!");
                let result = ${writer.format(generator.render())}().unmarshall(&message);
                assert!(result.is_ok(), "expected ok, got: {:?}", result);
                assert_eq!(
                    TestStream::MessageWithBlob(
                        MessageWithBlob::builder().data(Blob::new(&b"hello, world!"[..])).build()
                    ),
                    expect_event(result.unwrap())
                );
                """,
                "message_with_blob",
            )

            writer.unitTest(
                """
                let message = msg("event", "MessageWithString", "text/plain", b"hello, world!");
                let result = ${writer.format(generator.render())}().unmarshall(&message);
                assert!(result.is_ok(), "expected ok, got: {:?}", result);
                assert_eq!(
                    TestStream::MessageWithString(MessageWithString::builder().data("hello, world!").build()),
                    expect_event(result.unwrap())
                );
                """,
                "message_with_string",
            )

            writer.unitTest(
                """
                let message = msg(
                    "event",
                    "MessageWithStruct",
                    "${testCase.responseContentType}",
                    br#"${testCase.validTestStruct}"#
                );
                let result = ${writer.format(generator.render())}().unmarshall(&message);
                assert!(result.is_ok(), "expected ok, got: {:?}", result);
                assert_eq!(
                    TestStream::MessageWithStruct(MessageWithStruct::builder().some_struct(
                        TestStruct::builder()
                            .some_string("hello")
                            .some_int(5)
                            .build()
                    ).build()),
                    expect_event(result.unwrap())
                );
                """,
                "message_with_struct",
            )

            writer.unitTest(
                """
                let message = msg(
                    "event",
                    "MessageWithUnion",
                    "${testCase.responseContentType}",
                    br#"${testCase.validTestUnion}"#
                );
                let result = ${writer.format(generator.render())}().unmarshall(&message);
                assert!(result.is_ok(), "expected ok, got: {:?}", result);
                assert_eq!(
                    TestStream::MessageWithUnion(MessageWithUnion::builder().some_union(
                        TestUnion::Foo("hello".into())
                    ).build()),
                    expect_event(result.unwrap())
                );
                """,
                "message_with_union",
            )

            writer.unitTest(
                """
                let message = msg("event", "MessageWithHeaders", "application/octet-stream", b"")
                    .add_header(Header::new("blob", HeaderValue::ByteArray((&b"test"[..]).into())))
                    .add_header(Header::new("boolean", HeaderValue::Bool(true)))
                    .add_header(Header::new("byte", HeaderValue::Byte(55i8)))
                    .add_header(Header::new("int", HeaderValue::Int32(100_000i32)))
                    .add_header(Header::new("long", HeaderValue::Int64(9_000_000_000i64)))
                    .add_header(Header::new("short", HeaderValue::Int16(16_000i16)))
                    .add_header(Header::new("string", HeaderValue::String("test".into())))
                    .add_header(Header::new("timestamp", HeaderValue::Timestamp(Instant::from_epoch_seconds(5))));
                let result = ${writer.format(generator.render())}().unmarshall(&message);
                assert!(result.is_ok(), "expected ok, got: {:?}", result);
                assert_eq!(
                    TestStream::MessageWithHeaders(MessageWithHeaders::builder()
                        .blob(Blob::new(&b"test"[..]))
                        .boolean(true)
                        .byte(55i8)
                        .int(100_000i32)
                        .long(9_000_000_000i64)
                        .short(16_000i16)
                        .string("test")
                        .timestamp(Instant::from_epoch_seconds(5))
                        .build()
                    ),
                    expect_event(result.unwrap())
                );
                """,
                "message_with_headers",
            )

            writer.unitTest(
                """
                let message = msg("event", "MessageWithHeaderAndPayload", "application/octet-stream", b"payload")
                    .add_header(Header::new("header", HeaderValue::String("header".into())));
                let result = ${writer.format(generator.render())}().unmarshall(&message);
                assert!(result.is_ok(), "expected ok, got: {:?}", result);
                assert_eq!(
                    TestStream::MessageWithHeaderAndPayload(MessageWithHeaderAndPayload::builder()
                        .header("header")
                        .payload(Blob::new(&b"payload"[..]))
                        .build()
                    ),
                    expect_event(result.unwrap())
                );
                """,
                "message_with_header_and_payload",
            )

            writer.unitTest(
                """
                let message = msg(
                    "event",
                    "MessageWithNoHeaderPayloadTraits",
                    "${testCase.responseContentType}",
                    br#"${testCase.validMessageWithNoHeaderPayloadTraits}"#
                );
                let result = ${writer.format(generator.render())}().unmarshall(&message);
                assert!(result.is_ok(), "expected ok, got: {:?}", result);
                assert_eq!(
                    TestStream::MessageWithNoHeaderPayloadTraits(MessageWithNoHeaderPayloadTraits::builder()
                        .some_int(5)
                        .some_string("hello")
                        .build()
                    ),
                    expect_event(result.unwrap())
                );
                """,
                "message_with_no_header_payload_traits",
            )

            writer.unitTest(
                """
                let message = msg(
                    "exception",
                    "SomeError",
                    "${testCase.responseContentType}",
                    br#"${testCase.validSomeError}"#
                );
                let result = ${writer.format(generator.render())}().unmarshall(&message);
                assert!(result.is_ok(), "expected ok, got: {:?}", result);
                match expect_error(result.unwrap()).kind {
                    TestStreamOpErrorKind::SomeError(err) => assert_eq!(Some("some error"), err.message()),
                    kind => panic!("expected SomeError, but got {:?}", kind),
                }
                """,
                "some_error",
            )

            writer.unitTest(
                """
                let message = msg(
                    "exception",
                    "UnmodeledError",
                    "${testCase.responseContentType}",
                    br#"${testCase.validUnmodeledError}"#
                );
                let result = ${writer.format(generator.render())}().unmarshall(&message);
                assert!(result.is_ok(), "expected ok, got: {:?}", result);
                match expect_error(result.unwrap()).kind {
                    TestStreamOpErrorKind::Unhandled(err) => {
                        assert!(format!("{}", err).contains("message: \"unmodeled error\""));
                    },
                    kind => panic!("expected generic error, but got {:?}", kind),
                }
                """,
                "generic_error",
            )

            writer.unitTest(
                """
                let message = msg(
                    "event",
                    "MessageWithBlob",
                    "wrong-content-type",
                    br#"${testCase.validTestStruct}"#
                );
                let result = ${writer.format(generator.render())}().unmarshall(&message);
                assert!(result.is_err(), "expected error, got: {:?}", result);
                assert!(format!("{}", result.err().unwrap()).contains("expected :content-type to be"));
                """,
                "bad_content_type",
            )
        }
        test.project.compileAndTest()
    }
}
