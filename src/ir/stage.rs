use crate::analysis::inference::TypedCrate;
use crate::analysis::resolver::GlobalName;
use crate::ir::{anf, constructor, decision_tree, monomorphization, pattern};

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

/// Marker type for ANF IR stage.
pub struct AnfStage;

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

impl IrStage for AnfStage {
    type Output = anf::Crate;

    fn convert(typed: TypedCrate, base_id: GlobalName) -> Self::Output {
        let constructor_ir = constructor::convert(typed, base_id);
        let pattern_ir = pattern::convert(constructor_ir);
        let decision_tree_ir = decision_tree::lower_crate(pattern_ir);
        anf::lower_crate(decision_tree_ir)
    }
}

/// Trait for whole-program IR compilation stages.
///
/// Unlike `IrStage` which operates on a single crate, this trait is for
/// stages that require the entire program (all crates + main entry point).
pub trait ProgramStage {
    type Output;

    fn convert(crates: Vec<anf::Crate>, main_name: GlobalName) -> Self::Output;
}

/// Marker type for monomorphized IR stage.
pub struct MonomorphizedStage;

impl ProgramStage for MonomorphizedStage {
    type Output = monomorphization::Program;

    fn convert(crates: Vec<anf::Crate>, main_name: GlobalName) -> Self::Output {
        let accumulated = monomorphization::accumulate(crates, main_name);
        monomorphization::monomorphize(accumulated)
    }
}
