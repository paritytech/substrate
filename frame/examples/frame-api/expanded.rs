explicit
scrate_decl #[doc(hidden)] mod sp_api_hidden_includes_construct_runtime
{ pub use frame :: deps :: frame_support as hidden_include ; }
1
2
3
4
done
#[doc(hidden)] mod sp_api_hidden_includes_construct_runtime
{ pub use frame :: deps :: frame_support as hidden_include ; } const _ : () =
{
    #[allow(unused)] type __hidden_use_of_unchecked_extrinsic =
    UncheckedExtrinsic ;
} ;
#[derive(Clone, Copy, PartialEq, Eq, self ::
sp_api_hidden_includes_construct_runtime :: hidden_include :: sp_runtime ::
RuntimeDebug, self :: sp_api_hidden_includes_construct_runtime ::
hidden_include :: scale_info :: TypeInfo)] pub struct Test ; impl self ::
sp_api_hidden_includes_construct_runtime :: hidden_include :: sp_runtime ::
traits :: GetNodeBlockType for Test { type NodeBlock = Block ; } impl self ::
sp_api_hidden_includes_construct_runtime :: hidden_include :: sp_runtime ::
traits :: GetRuntimeBlockType for Test { type RuntimeBlock = Block ; }
#[doc(hidden)] trait InternalConstructRuntime
{
    #[inline(always)] fn runtime_metadata(& self) -> self ::
    sp_api_hidden_includes_construct_runtime :: hidden_include :: sp_std ::
    vec :: Vec < self :: sp_api_hidden_includes_construct_runtime ::
    hidden_include :: metadata_ir :: RuntimeApiMetadataIR >
    { Default :: default() }
} #[doc(hidden)] impl InternalConstructRuntime for & Test {} frame_system ::
__substrate_event_check :: is_event_part_defined! (System) ;
#[derive(Clone, PartialEq, Eq, self ::
sp_api_hidden_includes_construct_runtime :: hidden_include :: codec :: Encode,
self :: sp_api_hidden_includes_construct_runtime :: hidden_include :: codec ::
Decode, self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
scale_info :: TypeInfo, self :: sp_api_hidden_includes_construct_runtime ::
hidden_include :: RuntimeDebug,)] #[allow(non_camel_case_types)] pub enum
RuntimeEvent { #[codec(index = 0u8)] System(frame_system :: Event < Test >), }
impl From < frame_system :: Event :: < Test > > for RuntimeEvent
{
    fn from(x : frame_system :: Event :: < Test >) -> Self
    { RuntimeEvent :: System(x) }
} impl TryInto < frame_system :: Event :: < Test > > for RuntimeEvent
{
    type Error = () ; fn try_into(self) -> self ::
    sp_api_hidden_includes_construct_runtime :: hidden_include :: sp_std ::
    result :: Result < frame_system :: Event :: < Test >, Self :: Error >
    { match self { Self :: System(evt) => Ok(evt), _ => Err(()), } }
} #[doc = r" The runtime origin type representing the origin of a call."]
#[doc = r""]
#[doc =
" Origin is always created with the base filter configured in [`frame_system::Config::BaseCallFilter`]."]
#[derive(Clone)] pub struct RuntimeOrigin
{
    caller : OriginCaller, filter : self ::
    sp_api_hidden_includes_construct_runtime :: hidden_include :: sp_std :: rc
    :: Rc < Box < dyn Fn(& < Test as frame_system :: Config > :: RuntimeCall)
    -> bool >>,
} #[cfg(not(feature = "std"))] impl self ::
sp_api_hidden_includes_construct_runtime :: hidden_include :: sp_std :: fmt ::
Debug for RuntimeOrigin
{
    fn
    fmt(& self, fmt : & mut self :: sp_api_hidden_includes_construct_runtime
    :: hidden_include :: sp_std :: fmt :: Formatter,) -> self ::
    sp_api_hidden_includes_construct_runtime :: hidden_include :: sp_std ::
    result :: Result < (), self :: sp_api_hidden_includes_construct_runtime ::
    hidden_include :: sp_std :: fmt :: Error >
    { fmt.write_str("<wasm:stripped>") }
} #[cfg(feature = "std")] impl self ::
sp_api_hidden_includes_construct_runtime :: hidden_include :: sp_std :: fmt ::
Debug for RuntimeOrigin
{
    fn
    fmt(& self, fmt : & mut self :: sp_api_hidden_includes_construct_runtime
    :: hidden_include :: sp_std :: fmt :: Formatter,) -> self ::
    sp_api_hidden_includes_construct_runtime :: hidden_include :: sp_std ::
    result :: Result < (), self :: sp_api_hidden_includes_construct_runtime ::
    hidden_include :: sp_std :: fmt :: Error >
    {
        fmt.debug_struct("Origin").field("caller", &
        self.caller).field("filter", & "[function ptr]").finish()
    }
} impl self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
traits :: OriginTrait for RuntimeOrigin
{
    type Call = < Test as frame_system :: Config > :: RuntimeCall ; type
    PalletsOrigin = OriginCaller ; type AccountId = < Test as frame_system ::
    Config > :: AccountId ; fn
    add_filter(& mut self, filter : impl Fn(& Self :: Call) -> bool + 'static)
    {
        let f = self.filter.clone() ; self.filter = self ::
        sp_api_hidden_includes_construct_runtime :: hidden_include :: sp_std
        :: rc :: Rc ::
        new(Box :: new(move | call | { f(call) && filter(call) })) ;
    } fn reset_filter(& mut self)
    {
        let filter = < < Test as frame_system :: Config > :: BaseCallFilter as
        self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
        traits :: Contains << Test as frame_system :: Config > :: RuntimeCall
        > > :: contains ; self.filter = self ::
        sp_api_hidden_includes_construct_runtime :: hidden_include :: sp_std
        :: rc :: Rc :: new(Box :: new(filter)) ;
    } fn set_caller_from(& mut self, other : impl Into < Self >)
    { self.caller = other.into().caller ; } fn
    filter_call(& self, call : & Self :: Call) -> bool
    {
        match self.caller
        {
            OriginCaller :: system(frame_system :: Origin :: < Test > :: Root)
            => true, _ => (self.filter) (call),
        }
    } fn caller(& self) -> & Self :: PalletsOrigin { & self.caller } fn
    into_caller(self) -> Self :: PalletsOrigin { self.caller } fn
    try_with_caller < R >
    (mut self, f : impl FnOnce(Self :: PalletsOrigin) -> Result < R, Self ::
    PalletsOrigin >,) -> Result < R, Self >
    {
        match f(self.caller)
        {
            Ok(r) => Ok(r), Err(caller) =>
            { self.caller = caller ; Err(self) }
        }
    } fn none() -> Self { frame_system :: RawOrigin :: None.into() } fn root()
    -> Self { frame_system :: RawOrigin :: Root.into() } fn
    signed(by : Self :: AccountId) -> Self
    { frame_system :: RawOrigin :: Signed(by).into() }
}
#[derive(Clone, PartialEq, Eq, self ::
sp_api_hidden_includes_construct_runtime :: hidden_include :: RuntimeDebug,
self :: sp_api_hidden_includes_construct_runtime :: hidden_include :: codec ::
Encode, self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
codec :: Decode, self :: sp_api_hidden_includes_construct_runtime ::
hidden_include :: scale_info :: TypeInfo, self ::
sp_api_hidden_includes_construct_runtime :: hidden_include :: codec ::
MaxEncodedLen,)] #[allow(non_camel_case_types)] pub enum OriginCaller
{
    #[codec(index = 0u8)] system(frame_system :: Origin < Test >),
    #[allow(dead_code)]
    Void(self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
    Void)
} #[allow(dead_code)] impl RuntimeOrigin
{
    #[doc =
    " Create with system none origin and [`frame_system::Config::BaseCallFilter`]."]
    pub fn none() -> Self
    {
        < RuntimeOrigin as self :: sp_api_hidden_includes_construct_runtime ::
        hidden_include :: traits :: OriginTrait > :: none()
    }
    #[doc =
    " Create with system root origin and [`frame_system::Config::BaseCallFilter`]."]
    pub fn root() -> Self
    {
        < RuntimeOrigin as self :: sp_api_hidden_includes_construct_runtime ::
        hidden_include :: traits :: OriginTrait > :: root()
    }
    #[doc =
    " Create with system signed origin and [`frame_system::Config::BaseCallFilter`]."]
    pub fn signed(by : < Test as frame_system :: Config > :: AccountId) ->
    Self
    {
        < RuntimeOrigin as self :: sp_api_hidden_includes_construct_runtime ::
        hidden_include :: traits :: OriginTrait > :: signed(by)
    }
} impl From < frame_system :: Origin < Test >> for OriginCaller
{
    fn from(x : frame_system :: Origin < Test >) -> Self
    { OriginCaller :: system(x) }
} impl self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
traits :: CallerTrait << Test as frame_system :: Config > :: AccountId > for
OriginCaller
{
    fn into_system(self) -> Option < frame_system :: RawOrigin << Test as
    frame_system :: Config > :: AccountId >>
    { match self { OriginCaller :: system(x) => Some(x), _ => None, } } fn
    as_system_ref(& self) -> Option < & frame_system :: RawOrigin << Test as
    frame_system :: Config > :: AccountId >>
    { match & self { OriginCaller :: system(o) => Some(o), _ => None, } }
} impl TryFrom < OriginCaller > for frame_system :: Origin < Test >
{
    type Error = OriginCaller ; fn try_from(x : OriginCaller) -> self ::
    sp_api_hidden_includes_construct_runtime :: hidden_include :: sp_std ::
    result :: Result < frame_system :: Origin < Test >, OriginCaller >
    { if let OriginCaller :: system(l) = x { Ok(l) } else { Err(x) } }
} impl From < frame_system :: Origin < Test >> for RuntimeOrigin
{
    #[doc =
    " Convert to runtime origin, using as filter: [`frame_system::Config::BaseCallFilter`]."]
    fn from(x : frame_system :: Origin < Test >) -> Self
    { let o : OriginCaller = x.into() ; o.into() }
} impl From < OriginCaller > for RuntimeOrigin
{
    fn from(x : OriginCaller) -> Self
    {
        let mut o = RuntimeOrigin
        {
            caller : x, filter : self ::
            sp_api_hidden_includes_construct_runtime :: hidden_include ::
            sp_std :: rc :: Rc :: new(Box :: new(| _ | true)),
        } ; self :: sp_api_hidden_includes_construct_runtime :: hidden_include
        :: traits :: OriginTrait :: reset_filter(& mut o) ; o
    }
} impl From < RuntimeOrigin > for self ::
sp_api_hidden_includes_construct_runtime :: hidden_include :: sp_std :: result
:: Result < frame_system :: Origin < Test >, RuntimeOrigin >
{
    #[doc =
    r" NOTE: converting to pallet origin loses the origin filter information."]
    fn from(val : RuntimeOrigin) -> Self
    {
        if let OriginCaller :: system(l) = val.caller { Ok(l) } else
        { Err(val) }
    }
} impl From < Option << Test as frame_system :: Config > :: AccountId >> for
RuntimeOrigin
{
    #[doc =
    " Convert to runtime origin with caller being system signed or none and use filter [`frame_system::Config::BaseCallFilter`]."]
    fn from(x : Option << Test as frame_system :: Config > :: AccountId >) ->
    Self { < frame_system :: Origin < Test >> :: from(x).into() }
} pub type System = frame_system :: Pallet < Test > ;
#[doc = r" All pallets included in the runtime as a nested tuple of types."]
#[deprecated(note =
"The type definition has changed from representing all pallets \
			excluding system, in reversed order to become the representation of all pallets \
			including system pallet in regular order. For this reason it is encouraged to use \
			explicitly one of `AllPalletsWithSystem`, `AllPalletsWithoutSystem`, \
			`AllPalletsWithSystemReversed`, `AllPalletsWithoutSystemReversed`. \
			Note that the type `frame_executive::Executive` expects one of `AllPalletsWithSystem` \
			, `AllPalletsWithSystemReversed`, `AllPalletsReversedWithSystemFirst`. More details in \
			https://github.com/paritytech/substrate/pull/10043")]
pub type AllPallets = AllPalletsWithSystem ; #[cfg(all())]
#[doc = r" All pallets included in the runtime as a nested tuple of types."]
pub type AllPalletsWithSystem = (System,) ; #[cfg(all())]
#[doc = r" All pallets included in the runtime as a nested tuple of types."]
#[doc = r" Excludes the System pallet."] pub type AllPalletsWithoutSystem = ()
; #[cfg(all())]
#[doc =
r" All pallets included in the runtime as a nested tuple of types in reversed order."]
#[deprecated(note =
"Using reverse pallet orders is deprecated. use only \
			`AllPalletsWithSystem or AllPalletsWithoutSystem`")]
pub type AllPalletsWithSystemReversed = (System,) ; #[cfg(all())]
#[doc =
r" All pallets included in the runtime as a nested tuple of types in reversed order."]
#[doc = r" Excludes the System pallet."]
#[deprecated(note =
"Using reverse pallet orders is deprecated. use only \
			`AllPalletsWithSystem or AllPalletsWithoutSystem`")]
pub type AllPalletsWithoutSystemReversed = () ; #[cfg(all())]
#[doc =
r" All pallets included in the runtime as a nested tuple of types in reversed order."]
#[doc = r" With the system pallet first."]
#[deprecated(note =
"Using reverse pallet orders is deprecated. use only \
			`AllPalletsWithSystem or AllPalletsWithoutSystem`")]
pub type AllPalletsReversedWithSystemFirst = (System,) ;
#[doc = r" Provides an implementation of `PalletInfo` to provide information"]
#[doc = r" about the pallet setup in the runtime."] pub struct PalletInfo ;
impl self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
traits :: PalletInfo for PalletInfo
{
    fn index < P : 'static > () -> Option < usize >
    {
        let type_id = self :: sp_api_hidden_includes_construct_runtime ::
        hidden_include :: sp_std :: any :: TypeId :: of :: < P > () ; if
        type_id == self :: sp_api_hidden_includes_construct_runtime ::
        hidden_include :: sp_std :: any :: TypeId :: of :: < System > ()
        { return Some(0usize) } None
    } fn name < P : 'static > () -> Option < & 'static str >
    {
        let type_id = self :: sp_api_hidden_includes_construct_runtime ::
        hidden_include :: sp_std :: any :: TypeId :: of :: < P > () ; if
        type_id == self :: sp_api_hidden_includes_construct_runtime ::
        hidden_include :: sp_std :: any :: TypeId :: of :: < System > ()
        { return Some("System") } None
    } fn module_name < P : 'static > () -> Option < & 'static str >
    {
        let type_id = self :: sp_api_hidden_includes_construct_runtime ::
        hidden_include :: sp_std :: any :: TypeId :: of :: < P > () ; if
        type_id == self :: sp_api_hidden_includes_construct_runtime ::
        hidden_include :: sp_std :: any :: TypeId :: of :: < System > ()
        { return Some("frame_system") } None
    } fn crate_version < P : 'static > () -> Option < self ::
    sp_api_hidden_includes_construct_runtime :: hidden_include :: traits ::
    CrateVersion >
    {
        let type_id = self :: sp_api_hidden_includes_construct_runtime ::
        hidden_include :: sp_std :: any :: TypeId :: of :: < P > () ; if
        type_id == self :: sp_api_hidden_includes_construct_runtime ::
        hidden_include :: sp_std :: any :: TypeId :: of :: < System > ()
        {
            return
            Some(< frame_system :: Pallet < Test > as self ::
            sp_api_hidden_includes_construct_runtime :: hidden_include ::
            traits :: PalletInfoAccess > :: crate_version())
        } None
    }
} frame_system :: __substrate_call_check :: is_call_part_defined! (System) ;
#[derive(Clone, PartialEq, Eq, self ::
sp_api_hidden_includes_construct_runtime :: hidden_include :: codec :: Encode,
self :: sp_api_hidden_includes_construct_runtime :: hidden_include :: codec ::
Decode, self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
scale_info :: TypeInfo, self :: sp_api_hidden_includes_construct_runtime ::
hidden_include :: RuntimeDebug,)] pub enum RuntimeCall
{
    #[codec(index = 0u8)]
    System(self :: sp_api_hidden_includes_construct_runtime :: hidden_include
    :: dispatch :: CallableCallFor < System, Test >),
} #[cfg(test)] impl RuntimeCall
{
    #[doc =
    r" Return a list of the module names together with their size in memory."]
    pub const fn sizes() -> & 'static [(& 'static str, usize)]
    {
        use self :: sp_api_hidden_includes_construct_runtime :: hidden_include
        :: dispatch :: Callable ; use core :: mem :: size_of ; &
        [(stringify! (System), size_of :: < < System as Callable < Test >> ::
        RuntimeCall > (),),]
    }
    #[doc =
    r" Panics with diagnostic information if the size is greater than the given `limit`."]
    pub fn assert_size_under(limit : usize)
    {
        let size = core :: mem :: size_of :: < Self > () ; let call_oversize =
        size > limit ; if call_oversize
        {
            println!
            ("Size of `Call` is {} bytes (provided limit is {} bytes)", size,
            limit) ; let mut sizes = Self :: sizes().to_vec() ;
            sizes.sort_by_key(| x | - (x.1 as isize)) ; for(i, & (name, size))
            in sizes.iter().enumerate().take(5)
            { println! ("Offender #{}: {} at {} bytes", i + 1, name, size) ; }
            if let Some((_, next_size)) = sizes.get(5)
            {
                println!
                ("{} others of size {} bytes or less", sizes.len() - 5,
                next_size) ;
            } panic!
            ("Size of `Call` is more than limit; use `Box` on complex parameter types to reduce the
						size of `Call`.
						If the limit is too strong, maybe consider providing a higher limit.")
            ;
        }
    }
} impl self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
dispatch :: GetDispatchInfo for RuntimeCall
{
    fn get_dispatch_info(& self) -> self ::
    sp_api_hidden_includes_construct_runtime :: hidden_include :: dispatch ::
    DispatchInfo
    {
        match self
        { RuntimeCall :: System(call) => call.get_dispatch_info(), }
    }
} #[allow(deprecated)] impl self :: sp_api_hidden_includes_construct_runtime
:: hidden_include :: weights :: GetDispatchInfo for RuntimeCall {} impl self
:: sp_api_hidden_includes_construct_runtime :: hidden_include :: dispatch ::
GetCallMetadata for RuntimeCall
{
    fn get_call_metadata(& self) -> self ::
    sp_api_hidden_includes_construct_runtime :: hidden_include :: dispatch ::
    CallMetadata
    {
        use self :: sp_api_hidden_includes_construct_runtime :: hidden_include
        :: dispatch :: GetCallName ; match self
        {
            RuntimeCall :: System(call) =>
            {
                let function_name = call.get_call_name() ; let pallet_name =
                stringify! (System) ; self ::
                sp_api_hidden_includes_construct_runtime :: hidden_include ::
                dispatch :: CallMetadata { function_name, pallet_name }
            }
        }
    } fn get_module_names() -> & 'static [& 'static str]
    { & [stringify! (System),] } fn get_call_names(module : & str) -> &
    'static [& 'static str]
    {
        use self :: sp_api_hidden_includes_construct_runtime :: hidden_include
        :: dispatch :: { Callable, GetCallName } ; match module
        {
            stringify! (System) => << System as Callable < Test >> ::
            RuntimeCall as GetCallName > :: get_call_names(), _ =>
            unreachable! (),
        }
    }
} impl self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
dispatch :: Dispatchable for RuntimeCall
{
    type RuntimeOrigin = RuntimeOrigin ; type Config = RuntimeCall ; type Info
    = self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
    dispatch :: DispatchInfo ; type PostInfo = self ::
    sp_api_hidden_includes_construct_runtime :: hidden_include :: dispatch ::
    PostDispatchInfo ; fn dispatch(self, origin : RuntimeOrigin) -> self ::
    sp_api_hidden_includes_construct_runtime :: hidden_include :: dispatch ::
    DispatchResultWithPostInfo
    {
        if! < Self :: RuntimeOrigin as self ::
        sp_api_hidden_includes_construct_runtime :: hidden_include :: traits
        :: OriginTrait > :: filter_call(& origin, & self)
        {
            return self :: sp_api_hidden_includes_construct_runtime ::
            hidden_include :: sp_std :: result :: Result ::
            Err(frame_system :: Error :: < Test > :: CallFiltered.into()) ;
        } self :: sp_api_hidden_includes_construct_runtime :: hidden_include
        :: traits :: UnfilteredDispatchable ::
        dispatch_bypass_filter(self, origin)
    }
} impl self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
traits :: UnfilteredDispatchable for RuntimeCall
{
    type RuntimeOrigin = RuntimeOrigin ; fn
    dispatch_bypass_filter(self, origin : RuntimeOrigin) -> self ::
    sp_api_hidden_includes_construct_runtime :: hidden_include :: dispatch ::
    DispatchResultWithPostInfo
    {
        match self
        {
            RuntimeCall :: System(call) => self ::
            sp_api_hidden_includes_construct_runtime :: hidden_include ::
            traits :: UnfilteredDispatchable ::
            dispatch_bypass_filter(call, origin),
        }
    }
} impl self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
traits :: IsSubType < self :: sp_api_hidden_includes_construct_runtime ::
hidden_include :: dispatch :: CallableCallFor < System, Test >> for
RuntimeCall
{
    #[allow(unreachable_patterns)] fn is_sub_type(& self) -> Option < & self
    :: sp_api_hidden_includes_construct_runtime :: hidden_include :: dispatch
    :: CallableCallFor < System, Test >>
    { match self { RuntimeCall :: System(call) => Some(call), _ => None, } }
} impl From < self :: sp_api_hidden_includes_construct_runtime ::
hidden_include :: dispatch :: CallableCallFor < System, Test >> for
RuntimeCall
{
    fn
    from(call : self :: sp_api_hidden_includes_construct_runtime ::
    hidden_include :: dispatch :: CallableCallFor < System, Test >) -> Self
    { RuntimeCall :: System(call) }
} impl Test
{
    fn metadata_ir() -> self :: sp_api_hidden_includes_construct_runtime ::
    hidden_include :: metadata_ir :: MetadataIR
    {
        let rt = Test ; self :: sp_api_hidden_includes_construct_runtime ::
        hidden_include :: metadata_ir :: MetadataIR
        {
            pallets : self :: sp_api_hidden_includes_construct_runtime ::
            hidden_include :: sp_std :: vec!
            [self :: sp_api_hidden_includes_construct_runtime ::
            hidden_include :: metadata_ir :: PalletMetadataIR
            {
                name : stringify! (System), index : 0u8, storage :
                Some(frame_system :: Pallet :: < Test > ::
                storage_metadata()), calls :
                Some(frame_system :: Pallet :: < Test > :: call_functions()),
                event :
                Some(self :: sp_api_hidden_includes_construct_runtime ::
                hidden_include :: metadata_ir :: PalletEventMetadataIR
                {
                    ty : self :: sp_api_hidden_includes_construct_runtime ::
                    hidden_include :: scale_info :: meta_type :: < frame_system
                    :: Event :: < Test > > ()
                }), constants : frame_system :: Pallet :: < Test > ::
                pallet_constants_metadata(), error : frame_system :: Pallet ::
                < Test > :: error_metadata(), docs : frame_system :: Pallet ::
                < Test > :: pallet_documentation_metadata(),
            }], extrinsic : self :: sp_api_hidden_includes_construct_runtime
            :: hidden_include :: metadata_ir :: ExtrinsicMetadataIR
            {
                ty : self :: sp_api_hidden_includes_construct_runtime ::
                hidden_include :: scale_info :: meta_type :: <
                UncheckedExtrinsic > (), version : < UncheckedExtrinsic as
                self :: sp_api_hidden_includes_construct_runtime ::
                hidden_include :: sp_runtime :: traits :: ExtrinsicMetadata >
                :: VERSION, signed_extensions : < < UncheckedExtrinsic as self
                :: sp_api_hidden_includes_construct_runtime :: hidden_include
                :: sp_runtime :: traits :: ExtrinsicMetadata > ::
                SignedExtensions as self ::
                sp_api_hidden_includes_construct_runtime :: hidden_include ::
                sp_runtime :: traits :: SignedExtension > ::
                metadata().into_iter().map(| meta | self ::
                sp_api_hidden_includes_construct_runtime :: hidden_include ::
                metadata_ir :: SignedExtensionMetadataIR
                {
                    identifier : meta.identifier, ty : meta.ty,
                    additional_signed : meta.additional_signed,
                }).collect(),
            }, ty : self :: sp_api_hidden_includes_construct_runtime ::
            hidden_include :: scale_info :: meta_type :: < Test > (), apis :
            (& rt).runtime_metadata(),
        }
    } pub fn metadata() -> self :: sp_api_hidden_includes_construct_runtime ::
    hidden_include :: metadata :: RuntimeMetadataPrefixed
    {
        self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
        metadata_ir :: into_latest(Test :: metadata_ir())
    } pub fn metadata_at_version(version : u32) -> Option < self ::
    sp_api_hidden_includes_construct_runtime :: hidden_include ::
    OpaqueMetadata >
    {
        self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
        metadata_ir ::
        into_version(Test :: metadata_ir(),
        version).map(| prefixed |
        {
            self :: sp_api_hidden_includes_construct_runtime :: hidden_include
            :: OpaqueMetadata :: new(prefixed.into())
        })
    } pub fn metadata_versions() -> self ::
    sp_api_hidden_includes_construct_runtime :: hidden_include :: sp_std ::
    vec :: Vec < u32 >
    {
        self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
        metadata_ir :: supported_versions()
    }
} #[cfg(any(feature = "std", test))] use self ::
sp_api_hidden_includes_construct_runtime :: hidden_include :: serde as
__genesis_config_serde_import__ ; #[cfg(any(feature = "std", test))]
#[derive(self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
serde :: Serialize, self :: sp_api_hidden_includes_construct_runtime ::
hidden_include :: serde :: Deserialize, Default)]
#[serde(rename_all = "camelCase")] #[serde(deny_unknown_fields)]
#[serde(crate = "__genesis_config_serde_import__")] pub struct
RuntimeGenesisConfig {} #[cfg(any(feature = "std", test))] pub type
GenesisConfig = RuntimeGenesisConfig ; #[cfg(any(feature = "std", test))] impl
self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
sp_runtime :: BuildStorage for RuntimeGenesisConfig
{
    fn
    assimilate_storage(& self, storage : & mut self ::
    sp_api_hidden_includes_construct_runtime :: hidden_include :: sp_runtime
    :: Storage,) -> std :: result :: Result < (), String >
    {
        self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
        BasicExternalities ::
        execute_with_storage(storage, ||
        {
            < AllPalletsWithSystem as self ::
            sp_api_hidden_includes_construct_runtime :: hidden_include ::
            traits :: OnGenesis > :: on_genesis() ;
        }) ; Ok(())
    }
} trait InherentDataExt
{
    fn create_extrinsics(& self) -> self ::
    sp_api_hidden_includes_construct_runtime :: hidden_include :: inherent ::
    Vec << Block as self :: sp_api_hidden_includes_construct_runtime ::
    hidden_include :: inherent :: BlockT > :: Extrinsic > ; fn
    check_extrinsics(& self, block : & Block) -> self ::
    sp_api_hidden_includes_construct_runtime :: hidden_include :: inherent ::
    CheckInherentsResult ;
} impl InherentDataExt for self :: sp_api_hidden_includes_construct_runtime ::
hidden_include :: inherent :: InherentData
{
    fn create_extrinsics(& self) -> self ::
    sp_api_hidden_includes_construct_runtime :: hidden_include :: inherent ::
    Vec << Block as self :: sp_api_hidden_includes_construct_runtime ::
    hidden_include :: inherent :: BlockT > :: Extrinsic >
    {
        use self :: sp_api_hidden_includes_construct_runtime :: hidden_include
        :: inherent :: ProvideInherent ; let mut inherents = Vec :: new() ;
        inherents
    } fn check_extrinsics(& self, block : & Block) -> self ::
    sp_api_hidden_includes_construct_runtime :: hidden_include :: inherent ::
    CheckInherentsResult
    {
        use self :: sp_api_hidden_includes_construct_runtime :: hidden_include
        :: inherent :: { ProvideInherent, IsFatalError } ; use self ::
        sp_api_hidden_includes_construct_runtime :: hidden_include :: traits
        :: { IsSubType, ExtrinsicCall } ; use self ::
        sp_api_hidden_includes_construct_runtime :: hidden_include ::
        sp_runtime :: traits :: Block as _ ; let mut result = self ::
        sp_api_hidden_includes_construct_runtime :: hidden_include :: inherent
        :: CheckInherentsResult :: new() ; for xt in block.extrinsics()
        {
            if self :: sp_api_hidden_includes_construct_runtime ::
            hidden_include :: inherent :: Extrinsic ::
            is_signed(xt).unwrap_or(false) { break } let mut is_inherent =
            false ; if! is_inherent { break }
        } result
    }
} impl self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
traits :: EnsureInherentsAreFirst < Block > for Test
{
    fn ensure_inherents_are_first(block : & Block) -> Result < (), u32 >
    {
        use self :: sp_api_hidden_includes_construct_runtime :: hidden_include
        :: inherent :: ProvideInherent ; use self ::
        sp_api_hidden_includes_construct_runtime :: hidden_include :: traits
        :: { IsSubType, ExtrinsicCall } ; use self ::
        sp_api_hidden_includes_construct_runtime :: hidden_include ::
        sp_runtime :: traits :: Block as _ ; let mut first_signed_observed =
        false ; for(i, xt) in block.extrinsics().iter().enumerate()
        {
            let is_signed = self :: sp_api_hidden_includes_construct_runtime
            :: hidden_include :: inherent :: Extrinsic ::
            is_signed(xt).unwrap_or(false) ; let is_inherent = if is_signed
            { false } else { let mut is_inherent = false ; is_inherent } ; if!
            is_inherent { first_signed_observed = true ; } if
            first_signed_observed && is_inherent { return Err(i as u32) }
        } Ok(())
    }
} impl self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
unsigned :: ValidateUnsigned for Test
{
    type Call = RuntimeCall ; fn pre_dispatch(call : & Self :: Call) -> Result
    < (), self :: sp_api_hidden_includes_construct_runtime :: hidden_include
    :: unsigned :: TransactionValidityError >
    { #[allow(unreachable_patterns)] match call { _ => Ok(()), } } fn
    validate_unsigned(#[allow(unused_variables)] source : self ::
    sp_api_hidden_includes_construct_runtime :: hidden_include :: unsigned ::
    TransactionSource, call : & Self :: Call,) -> self ::
    sp_api_hidden_includes_construct_runtime :: hidden_include :: unsigned ::
    TransactionValidity
    {
        #[allow(unreachable_patterns)] match call
        {
            _ => self :: sp_api_hidden_includes_construct_runtime ::
            hidden_include :: unsigned :: UnknownTransaction ::
            NoUnsignedValidator.into(),
        }
    }
} #[doc = r" A reason for placing a freeze on funds."]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, self ::
sp_api_hidden_includes_construct_runtime :: hidden_include :: codec :: Encode,
self :: sp_api_hidden_includes_construct_runtime :: hidden_include :: codec ::
Decode, self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
codec :: MaxEncodedLen, self :: sp_api_hidden_includes_construct_runtime ::
hidden_include :: scale_info :: TypeInfo, self ::
sp_api_hidden_includes_construct_runtime :: hidden_include :: RuntimeDebug,)]
pub enum RuntimeFreezeReason {}
#[doc = r" A reason for placing a hold on funds."]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, self ::
sp_api_hidden_includes_construct_runtime :: hidden_include :: codec :: Encode,
self :: sp_api_hidden_includes_construct_runtime :: hidden_include :: codec ::
Decode, self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
codec :: MaxEncodedLen, self :: sp_api_hidden_includes_construct_runtime ::
hidden_include :: scale_info :: TypeInfo, self ::
sp_api_hidden_includes_construct_runtime :: hidden_include :: RuntimeDebug,)]
pub enum RuntimeHoldReason {}
#[doc = r" An identifier for each lock placed on funds."]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, self ::
sp_api_hidden_includes_construct_runtime :: hidden_include :: codec :: Encode,
self :: sp_api_hidden_includes_construct_runtime :: hidden_include :: codec ::
Decode, self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
codec :: MaxEncodedLen, self :: sp_api_hidden_includes_construct_runtime ::
hidden_include :: scale_info :: TypeInfo, self ::
sp_api_hidden_includes_construct_runtime :: hidden_include :: RuntimeDebug,)]
pub enum RuntimeLockId {} #[doc = r" A reason for slashing funds."]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, self ::
sp_api_hidden_includes_construct_runtime :: hidden_include :: codec :: Encode,
self :: sp_api_hidden_includes_construct_runtime :: hidden_include :: codec ::
Decode, self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
codec :: MaxEncodedLen, self :: sp_api_hidden_includes_construct_runtime ::
hidden_include :: scale_info :: TypeInfo, self ::
sp_api_hidden_includes_construct_runtime :: hidden_include :: RuntimeDebug,)]
pub enum RuntimeSlashReason {} #[cfg(test)] mod
__construct_runtime_integrity_test
{
    use super :: * ; #[test] pub fn runtime_integrity_tests()
    {
        self :: sp_api_hidden_includes_construct_runtime :: hidden_include ::
        sp_tracing :: try_init_simple() ; < AllPalletsWithSystem as self ::
        sp_api_hidden_includes_construct_runtime :: hidden_include :: traits
        :: IntegrityTest > :: integrity_test() ;
    }
}
construct_runtime: true
