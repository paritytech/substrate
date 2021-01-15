use super::StorageLineTypeDef;
use quote::ToTokens;
use frame_support_procedural_tools::clean_type_string;

/// Environment variable that tells us to print pallet upgrade helper.
const PRINT_PALLET_UPGRADE: &str = "PRINT_PALLET_UPGRADE";

fn check_print_pallet_upgrade() -> bool {
	std::env::var(PRINT_PALLET_UPGRADE).is_ok()
}

/// Convert visibilty as now objects are defined in a module.
fn convert_vis(vis: &syn::Visibility) -> &'static str{
	match vis {
		syn::Visibility::Inherited => "pub(super)",
		syn::Visibility::Public(_) => "pub",
		_ => "/* TODO_VISIBILITY */",
	}
}

/// fn to convert to token stream then string using display and then call clean_type_string on it.
fn to_cleaned_string(t: impl quote::ToTokens) -> String {
	clean_type_string(&format!("{}", t.into_token_stream()))
}

/// Print an incomplete upgrade from decl_storage macro to new pallet attribute.
pub fn maybe_print_pallet_upgrade(def: &super::DeclStorageDefExt) {
	if !check_print_pallet_upgrade() {
		return
	}

	let scrate = &quote::quote!(frame_support);

	let config_gen = if def.optional_instance.is_some() {
		"<I: 'static = ()>"
	} else {
		Default::default()
	};

	let impl_gen = if def.optional_instance.is_some() {
		"<T: Config<I>, I: 'static>"
	} else {
		"<T: Config>"
	};

	let decl_gen = if def.optional_instance.is_some() {
		"<T, I=()>"
	} else {
		"<T>"
	};

	let full_decl_gen = if def.optional_instance.is_some() {
		"<T: Config<I>, I: 'static = ()>"
	} else {
		"<T: Config>"
	};

	let use_gen = if def.optional_instance.is_some() {
		"<T, I>"
	} else {
		"<T>"
	};

	let use_gen_tuple = if def.optional_instance.is_some() {
		"<(T, I)>"
	} else {
		"<T>"
	};

	let mut genesis_config = String::new();
	let mut genesis_build = String::new();

	let genesis_config_builder_def = super::genesis_config::BuilderDef::from_def(scrate, def);
	if !genesis_config_builder_def.blocks.is_empty() {
		let genesis_config_def = match super::genesis_config::GenesisConfigDef::from_def(def) {
			Ok(g) => g,
			Err(err) => {
				println!("Could not print upgrade due compile error: {:?}", err);
				return
			},
		};

		let genesis_config_impl_gen = if genesis_config_def.is_generic {
			impl_gen.clone()
		} else {
			Default::default()
		};

		let genesis_config_use_gen = if genesis_config_def.is_generic {
			use_gen.clone()
		} else {
			Default::default()
		};

		let genesis_config_decl_gen = if genesis_config_def.is_generic {
			if def.optional_instance.is_some() {
				"<T: Config<I>, I: 'static = ()>"
			} else {
				"<T: Config>"
			}
		} else {
			Default::default()
		};

		let mut genesis_config_decl_fields = String::new();
		let mut genesis_config_default_fields = String::new();
		for field in &genesis_config_def.fields {
			genesis_config_decl_fields.push_str(&format!("
		{attrs}pub {name}: {typ},",
				attrs = field.attrs.iter()
					.fold(String::new(), |res, attr| {
						format!("{}#[{}]
		",
						res, attr.to_token_stream())
					}),
				name = field.name,
				typ = to_cleaned_string(&field.typ),
			));

			genesis_config_default_fields.push_str(&format!("
				{name}: {default},",
				name = field.name,
				default = to_cleaned_string(&field.default),
			));
		}

		genesis_config = format!("
	#[pallet::genesis_config]
	pub struct GenesisConfig{genesis_config_decl_gen}
		// TODO_MAYBE_WHERE_CLAUSE
	{{{genesis_config_decl_fields}
	}}

	#[cfg(feature = \"std\")]
	impl{genesis_config_impl_gen} Default for GenesisConfig{genesis_config_use_gen}
		// TODO_MAYBE_WHERE_CLAUSE
	{{
		fn default() -> Self {{
			Self {{{genesis_config_default_fields}
			}}
		}}
	}}",
			genesis_config_decl_gen = genesis_config_decl_gen,
			genesis_config_decl_fields = genesis_config_decl_fields,
			genesis_config_impl_gen = genesis_config_impl_gen,
			genesis_config_default_fields = genesis_config_default_fields,
			genesis_config_use_gen = genesis_config_use_gen,
		);

		let genesis_config_build = genesis_config_builder_def.blocks.iter()
			.fold(String::new(), |res, block| {
				format!("{}
					{}",
					res,
					to_cleaned_string(block),
				)
			});

		genesis_build = format!("
	#[pallet::genesis_build]
	impl{impl_gen} GenesisBuild{use_gen} for GenesisConfig{genesis_config_use_gen}
		// TODO_MAYBE_WHERE_CLAUSE
	{{
		fn build(&self) {{{genesis_config_build}
		}}
	}}",
			impl_gen = impl_gen,
			use_gen = use_gen,
			genesis_config_use_gen = genesis_config_use_gen,
			genesis_config_build = genesis_config_build,
		);
	}

	let mut storages = String::new();
	for line in &def.storage_lines {
		let storage_vis = convert_vis(&line.visibility);

		let getter = if let Some(getter) = &line.getter {
			format!("
	#[pallet::getter(fn {getter})]",
				getter = getter
			)
		} else {
			Default::default()
		};

		let value_type = &line.value_type;

		let default_value_type_value = line.default_value.as_ref()
			.map(|default_expr| {
				format!("
	#[pallet::type_value]
	{storage_vis} fn DefaultFor{name} /* TODO_MAYBE_GENERICS */ () -> {value_type} {{
		{default_expr}
	}}
",
					name = line.name,
					storage_vis = storage_vis,
					value_type = to_cleaned_string(&line.value_type),
					default_expr = to_cleaned_string(&default_expr),
				)
			})
			.unwrap_or_else(|| String::new());

		let comma_query_kind = if line.is_option {
			if line.default_value.is_some() {
				", OptionQuery"
			} else {
				Default::default()
			}
		} else {
			", ValueQuery"
		};

		let comma_default_value_getter_name = line.default_value.as_ref()
			.map(|_| format!(", DefaultFor{}", line.name))
			.unwrap_or_else(|| String::new());

		let typ = match &line.storage_type {
			StorageLineTypeDef::Map(map) => {
				format!("StorageMap<_, {hasher}, {key}, {value_type}{comma_query_kind}\
					{comma_default_value_getter_name}>",
					hasher = &map.hasher.to_storage_hasher_struct(),
					key = to_cleaned_string(&map.key),
					value_type = to_cleaned_string(&value_type),
					comma_query_kind = comma_query_kind,
					comma_default_value_getter_name = comma_default_value_getter_name,
				)
			},
			StorageLineTypeDef::DoubleMap(double_map) => {
				format!("StorageDoubleMap<_, {hasher1}, {key1}, {hasher2}, {key2}, {value_type}\
					{comma_query_kind}{comma_default_value_getter_name}>",
					hasher1 = double_map.hasher1.to_storage_hasher_struct(),
					key1 = to_cleaned_string(&double_map.key1),
					hasher2 = double_map.hasher2.to_storage_hasher_struct(),
					key2 = to_cleaned_string(&double_map.key2),
					value_type = to_cleaned_string(&value_type),
					comma_query_kind = comma_query_kind,
					comma_default_value_getter_name = comma_default_value_getter_name,
				)
			},
			StorageLineTypeDef::Simple(_) => {
				format!("StorageValue<_, {value_type}{comma_query_kind}\
					{comma_default_value_getter_name}>",
					value_type = to_cleaned_string(&value_type),
					comma_query_kind = comma_query_kind,
					comma_default_value_getter_name = comma_default_value_getter_name,
				)
			},
		};

		let additional_comment = if line.is_option && line.default_value.is_some() {
			" // TODO: This type of storage is no longer supported: `OptionQuery` cannot be used \
			alongside a not-none value on empty storage. Please use `ValueQuery` instead."
		} else {
			""
		};

		storages.push_str(&format!("
{default_value_type_value}{doc}
	#[pallet::storage]{getter}
	{storage_vis} type {name}{full_decl_gen} = {typ};{additional_comment}",
			default_value_type_value = default_value_type_value,
			getter = getter,
			storage_vis = storage_vis,
			name = line.name,
			full_decl_gen = full_decl_gen,
			typ = typ,
			additional_comment = additional_comment,
			doc = line.doc_attrs.iter()
				.fold(String::new(), |mut res, attr| {
					if let syn::Meta::NameValue(name_value) = attr {
						if name_value.path.is_ident("doc") {
							if let syn::Lit::Str(string) = &name_value.lit {
								res = format!("{}
	///{}",
									res,
									string.value(),
								);
							}
						}
					}
					res
				}),
		));
	}

	let deprecated_instance_stuff = if def.optional_instance.is_some() {
		"
	/// Old name for default instance generated by decl_storage.
	#[deprecated(note=\"use `()` instead\")]
	pub type DefaultInstance = ();

	/// Old name for instance trait used by old macros.
	#[deprecated(note=\"use `'static` instead\")]
	pub trait Instance: 'static {}
	impl<I: 'static> Instance for I {}"
	} else {
		""
	};

	println!("
// Template for pallet upgrade for {pallet_name}

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {{
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	use super::*;

	#[pallet::config]
	pub trait Config{config_gen}: frame_system::Config
		// TODO_MAYBE_ADDITIONAL_BOUNDS_AND_WHERE_CLAUSE
	{{
		// TODO_ASSOCIATED_TYPE_AND_CONSTANTS
	}}

	{deprecated_instance_stuff}

	#[pallet::pallet]
	#[pallet::generate_store({store_vis} trait Store)]
	pub struct Pallet{decl_gen}(PhantomData{use_gen_tuple});

	#[pallet::interface]
	impl{impl_gen} Hooks<BlockNumberFor<T>> for Pallet{use_gen}
		// TODO_MAYBE_WHERE_CLAUSE
	{{
		// TODO_ON_FINALIZE
		// TODO_ON_INITIALIZE
		// TODO_ON_RUNTIME_UPGRADE
		// TODO_INTEGRITY_TEST
		// TODO_OFFCHAIN_WORKER
	}}

	#[pallet::call]
	impl{impl_gen} Pallet{use_gen}
		// TODO_MAYBE_WHERE_CLAUSE
	{{
		// TODO_UPGRADE_DISPATCHABLES
	}}

	#[pallet::inherent]
	// TODO_INHERENT

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	// TODO_EVENT

	// TODO_REMOVE_IF_NO_EVENT
	/// Old name generated by `decl_event`.
	#[deprecated(note=\"use `Event` instead\")]
	pub type RawEvent /* TODO_PUT_EVENT_GENERICS */ = Event /* TODO_PUT_EVENT_GENERICS */;

	#[pallet::error]
	// TODO_ERROR

	#[pallet::origin]
	// TODO_ORIGIN

	#[pallet::validate_unsigned]
	// TODO_VALIDATE_UNSIGNED

	{storages}

	{genesis_config}

	{genesis_build}
}}",
		config_gen = config_gen,
		store_vis = convert_vis(&def.visibility),
		impl_gen = impl_gen,
		use_gen = use_gen,
		use_gen_tuple = use_gen_tuple,
		decl_gen = decl_gen,
		storages = storages,
		genesis_config = genesis_config,
		genesis_build = genesis_build,
		pallet_name = def.crate_name,
		deprecated_instance_stuff = deprecated_instance_stuff,
	);
}
