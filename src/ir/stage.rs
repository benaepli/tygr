use crate::analysis::inference::TypedCrate;
use crate::analysis::resolver::GlobalName;
use crate::ir::{constructor, decision_tree, pattern};

/// Trait for IR compilation stages.
pub trait IrStage {
    type Output;

    fn convert(typed: TypedCrate, base_id: GlobalName) -> Self::Output;
}

/// Marker type for constructor IR stage.
pub struct ConstructorStage;

/// Marker type for pattern IR stage.
pub struct PatternStage;

/// Marker type for decision tree IR stage.
pub struct DecisionTreeStage;

impl IrStage for ConstructorStage {
    type Output = constructor::Crate;

    fn convert(typed: TypedCrate, base_id: GlobalName) -> Self::Output {
        constructor::convert(typed, base_id)
    }
}

impl IrStage for PatternStage {
    type Output = pattern::Crate;

    fn convert(typed: TypedCrate, base_id: GlobalName) -> Self::Output {
        let constructor_ir = constructor::convert(typed, base_id);
        pattern::convert(constructor_ir)
    }
}

impl IrStage for DecisionTreeStage {
    type Output = decision_tree::Crate;

    fn convert(typed: TypedCrate, base_id: GlobalName) -> Self::Output {
        let constructor_ir = constructor::convert(typed, base_id);
        let pattern_ir = pattern::convert(constructor_ir);
        decision_tree::lower_crate(pattern_ir)
    }
}
