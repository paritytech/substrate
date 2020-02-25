use sp_std::prelude::*;

use core::any::{Any, TypeId};
use codec::{Encode, Decode};

use crate::traits::Header;

struct CapabilitySet {
    caps: Vec<(TypeId, Box<dyn Any>)>
}

impl CapabilitySet {
    fn new() -> Self {
        Self { caps: Vec::new() }
	}
	
    fn register<T: Any>(&mut self, cap: T) {    
        self.caps.push((cap.type_id(), Box::new(cap)))
    }
    
    fn get<T: Any>(&self) -> Option<&T> {
        let type_id = TypeId::of::<T>();
        for (t, cap) in &self.caps {
            if *t == type_id {
                return (&(*cap)).downcast_ref::<T>()
            }
        }
        None
    }
}

impl Default for CapabilitySet {
	fn default() -> Self {
		Self::new()
	}
}

// we need to transport the capabilityset over the WASM barrier
impl Decode for CapabilitySet
{
    fn decode<I: Input>(value: &mut I) -> Result<Self, Error>{
        unimplemented!()
    }
}

/// execution context passed to e.g. offchain workers
pub struct ExecutionContext<BlockHeader: Header>{
	header: BlockHeader,
	capabilities: CapabilitySet,
}

impl<BlockHeader> ExecutionContext<BlockHeader>
where
    BlockHeader: Header
{
	fn block_number(&self) -> &<BlockHeader as Header>::Number {
		self.block_header().number()
	}

	fn block_header(&self) -> &BlockHeader {
        &self.header
    }

	fn capability<C: Any>(&self) -> Option<&C> {
        self.capabilities.get::<C>()
    }
}