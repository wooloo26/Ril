//! Primitive Source ingress from the sealed static evaluator's literal encoding.
//! Publication-specific structural views remain separate from object identity.
use super::{SourceScalar, SourceSchema, SourceTypesError, WorkLimit};
use crate::static_eval::constants::ConstantPool;
use ril_compiler_core::ids::{ConstGraphId, ConstRef};
use ril_ir::{constants::ConstNodeKind, core::Literal};

/// This is a projection of a sealed literal, not of a semantic runtime `Ty`.
/// In particular nonfinite floats need no fabricated source literal or header.
pub(crate) fn literal_schema(
    pool: &ConstantPool,
    reference: ConstRef,
    work: &mut WorkLimit,
) -> Result<Option<SourceSchema>, SourceTypesError> {
    work.charge(2)?;
    if reference.graph != ConstGraphId(0) {
        return Err(SourceTypesError::Unresolved);
    }
    let node = pool
        .nodes
        .get(reference.node.0 as usize)
        .ok_or(SourceTypesError::MissingNode)?;
    let ConstNodeKind::Literal(literal) = &node.kind else {
        // A collection's physical encoding cannot recover its declared view.
        return Ok(None);
    };
    let kind = match literal {
        Literal::Unit => SourceScalar::Unit,
        Literal::Bool(_) => SourceScalar::Bool,
        Literal::String(_) => SourceScalar::Str,
        Literal::Bytes(_) => SourceScalar::Bytes,
        Literal::BigInteger(_) => SourceScalar::BigInt,
        Literal::Float { bits: 32, .. } => SourceScalar::F32,
        Literal::Float { bits: 64, .. } => SourceScalar::F64,
        Literal::Float { .. } => return Err(SourceTypesError::Unresolved),
        Literal::Integer { .. } => {
            let name = node
                .integer_type
                .as_deref()
                .ok_or(SourceTypesError::Unresolved)?;
            work.text(name)?;
            match name {
                "int" => SourceScalar::Int,
                "i8" => SourceScalar::I8,
                "i16" => SourceScalar::I16,
                "i32" => SourceScalar::I32,
                "i64" => SourceScalar::I64,
                "i128" => SourceScalar::I128,
                "isize" => SourceScalar::Isize,
                "u8" => SourceScalar::U8,
                "u16" => SourceScalar::U16,
                "u32" => SourceScalar::U32,
                "u64" => SourceScalar::U64,
                "u128" => SourceScalar::U128,
                "usize" => SourceScalar::Usize,
                _ => return Err(SourceTypesError::Unresolved),
            }
        }
    };
    SourceSchema::scalar(kind, None, work).map(Some)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::static_eval::constants::ConstantNode;
    use ril_compiler_core::{
        ids::ConstNodeId,
        source::{FileId, Span},
    };

    fn fixture(kind: ConstNodeKind) -> (ConstantPool, ConstRef) {
        let mut pool = ConstantPool::default();
        pool.nodes.push(ConstantNode {
            kind,
            span: Span {
                file: FileId(0),
                start: 0,
                end: 0,
            },
            fixed_array_length: None,
            integer_type: None,
            mutable_fields: Default::default(),
            result_producer: None,
            result_receipt: None,
            result_type: None,
        });
        (
            pool,
            ConstRef {
                graph: ConstGraphId(0),
                node: ConstNodeId(0),
            },
        )
    }

    #[test]
    fn nonfinite_constant_encodings_keep_their_original_scalar_width() {
        for bits in [32, 64] {
            for value in [0.0, -0.0, f64::INFINITY, f64::NEG_INFINITY, f64::NAN] {
                let (pool, reference) =
                    fixture(ConstNodeKind::Literal(Literal::Float { value, bits }));
                let source = literal_schema(&pool, reference, &mut WorkLimit::new(4096))
                    .unwrap()
                    .unwrap();
                let expected = SourceSchema::scalar(
                    if bits == 32 {
                        SourceScalar::F32
                    } else {
                        SourceScalar::F64
                    },
                    None,
                    &mut WorkLimit::new(4096),
                )
                .unwrap();
                assert_eq!(
                    source.equivalent(&expected, &mut WorkLimit::new(4096)),
                    Ok(true)
                );
                let other = SourceSchema::scalar(
                    if bits == 32 {
                        SourceScalar::F64
                    } else {
                        SourceScalar::F32
                    },
                    None,
                    &mut WorkLimit::new(4096),
                )
                .unwrap();
                assert_eq!(
                    source.equivalent(&other, &mut WorkLimit::new(4096)),
                    Ok(false)
                );
            }
        }
    }

    #[test]
    fn constant_ingress_needs_a_real_literal_and_spends_its_shared_work() {
        let (pool, reference) = fixture(ConstNodeKind::Literal(Literal::Float {
            value: f64::NAN,
            bits: 32,
        }));
        let mut work = WorkLimit::new(4096);
        literal_schema(&pool, reference, &mut work)
            .unwrap()
            .unwrap();
        let used = 4096 - work.remaining();
        let mut exact = WorkLimit::new(used);
        literal_schema(&pool, reference, &mut exact)
            .unwrap()
            .unwrap();
        assert_eq!(exact.remaining(), 0);
        for short in [0, used - 1] {
            assert!(matches!(
                literal_schema(&pool, reference, &mut WorkLimit::new(short)),
                Err(SourceTypesError::BudgetExceeded)
            ));
        }
        for changed in [
            ConstRef {
                graph: ConstGraphId(1),
                ..reference
            },
            ConstRef {
                node: ConstNodeId(1),
                ..reference
            },
        ] {
            assert!(literal_schema(&pool, changed, &mut WorkLimit::new(4096)).is_err());
        }
        let (pool, reference) = fixture(ConstNodeKind::Array(vec![]));
        assert!(
            literal_schema(&pool, reference, &mut WorkLimit::new(4096))
                .unwrap()
                .is_none()
        );
        let (pool, reference) = fixture(ConstNodeKind::Literal(Literal::Float {
            value: 1.0,
            bits: 16,
        }));
        assert!(literal_schema(&pool, reference, &mut WorkLimit::new(4096)).is_err());
    }
}
