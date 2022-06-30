/// The ident used for the block generic parameter.
pub const BLOCK_GENERIC_IDENT: &str = "Block";

/// Unique identifier used to make the hidden includes unique for this macro.
pub const HIDDEN_INCLUDES_ID: &str = "DECL_RUNTIME_APIS";

/// The `core_trait` attribute.
pub const CORE_TRAIT_ATTRIBUTE: &str = "core_trait";
/// The `api_version` attribute.
///
/// Is used to set the current version of the trait.
pub const API_VERSION_ATTRIBUTE: &str = "api_version";
/// The `changed_in` attribute.
///
/// Is used when the function signature changed between different versions of a trait.
/// This attribute should be placed on the old signature of the function.
pub const CHANGED_IN_ATTRIBUTE: &str = "changed_in";
/// The `renamed` attribute.
///
/// Is used when a trait method was renamed.
pub const RENAMED_ATTRIBUTE: &str = "renamed";
/// All attributes that we support in the declaration of a runtime api trait.
pub const SUPPORTED_ATTRIBUTE_NAMES: &[&str] =
	&[CORE_TRAIT_ATTRIBUTE, API_VERSION_ATTRIBUTE, CHANGED_IN_ATTRIBUTE, RENAMED_ATTRIBUTE];
