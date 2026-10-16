use super::*;
use ril_runtime_api::abi::OutcomeTag;

#[test]
fn validation_keeps_partial_error_progress_and_rejects_impossible_reports() {
    let mut runtime = Runtime::default();
    let data = runtime
        .allocate(Object::Bytes(b"abcd".to_vec().into()))
        .unwrap();
    let error = runtime
        .io_error("BrokenPipe", "after prefix", None)
        .unwrap();
    let partial = runtime.write_progress(2, Some(error)).unwrap();
    runtime.validate_write(partial, data).unwrap();
    let written = runtime.field(partial, "written").unwrap();
    assert_eq!(runtime.as_integer(written).unwrap(), 2);
    let excess = runtime.write_progress(5, Some(error)).unwrap();
    assert_eq!(
        runtime.validate_write(excess, data).unwrap_err().tag,
        OutcomeTag::LanguagePanic
    );
    let no_progress = runtime.write_progress(0, None).unwrap();
    assert_eq!(
        runtime.validate_write(no_progress, data).unwrap_err().tag,
        OutcomeTag::LanguagePanic
    );
    let empty = runtime.allocate(Object::Bytes(vec![].into())).unwrap();
    runtime.validate_write(no_progress, empty).unwrap();
    let negative = runtime.int(-1).unwrap();
    runtime
        .set_field(partial, "written".into(), negative)
        .unwrap();
    assert_eq!(
        runtime.validate_write(partial, data).unwrap_err().tag,
        OutcomeTag::LanguagePanic
    );
}

#[test]
fn reads_distinguish_zero_validation_eof_data_and_failure() {
    let mut runtime = Runtime::default();
    let zero = runtime.int(0).unwrap();
    let one = runtime.int(1).unwrap();
    let empty = runtime.read_chunk_value(vec![], false).unwrap();
    let empty = runtime.variant("Ok", vec![empty]).unwrap();
    runtime.validate_read(empty, zero).unwrap();
    assert_eq!(
        runtime.validate_read(empty, one).unwrap_err().tag,
        OutcomeTag::LanguagePanic
    );
    let eof = runtime.read_chunk_value(vec![], true).unwrap();
    let eof = runtime.variant("Ok", vec![eof]).unwrap();
    runtime.validate_read(eof, one).unwrap();
    assert_eq!(
        runtime.validate_read(eof, zero).unwrap_err().tag,
        OutcomeTag::LanguagePanic
    );
    let last = runtime.read_chunk_value(vec![255], true).unwrap();
    let last = runtime.variant("Ok", vec![last]).unwrap();
    runtime.validate_read(last, one).unwrap();
    assert_eq!(
        runtime.validate_read(last, zero).unwrap_err().tag,
        OutcomeTag::LanguagePanic
    );
    let failure = runtime.io_failure("Closed", "closed stream").unwrap();
    runtime.validate_read(failure, zero).unwrap();
    runtime.validate_read(failure, one).unwrap();
}

#[test]
fn suffix_and_accumulation_survive_source_collection_without_duplicate_prefixes() {
    let mut runtime = Runtime::default();
    let data = runtime
        .allocate(Object::Bytes(b"abcdef".to_vec().into()))
        .unwrap();
    let count = runtime.int(2).unwrap();
    let suffix = runtime
        .io_builtin("__io_bytes_suffix", &[data, count])
        .unwrap();
    runtime.root(0, suffix).unwrap();
    let accumulator = runtime.io_builtin("__io_acc_new", &[]).unwrap();
    runtime.root(1, accumulator).unwrap();
    runtime.statement_end();
    runtime.collect().unwrap();
    runtime
        .io_builtin("__io_acc_push", &[accumulator, suffix])
        .unwrap();
    let result = runtime
        .io_builtin("__io_acc_finish", &[accumulator])
        .unwrap();
    runtime.root(2, result).unwrap();
    runtime.statement_end();
    runtime.collect().unwrap();
    assert_eq!(runtime.as_bytes(result).unwrap(), b"cdef");
    assert_eq!(runtime.as_bytes(suffix).unwrap(), b"cdef");
    assert!(runtime.heap.deep_clone(accumulator).is_err());
}
