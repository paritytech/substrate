use crate::{context::Context, Config};
use ibc::{
	applications::transfer::{
		MODULE_ID_STR as TRANSFER_MODULE_ID, PORT_ID_STR as TRANSFER_PORT_ID,
	},
	core::{
		ics05_port::{context::PortReader, error::PortError},
		ics24_host::identifier::PortId,
		ics26_routing::context::ModuleId,
	},
};
use sp_std::str::FromStr;

impl<T: Config> PortReader for Context<T> {
	fn lookup_module_by_port(&self, port_id: &PortId) -> Result<ModuleId, PortError> {
		match port_id.as_str() {
			TRANSFER_PORT_ID => Ok(ModuleId::from_str(TRANSFER_MODULE_ID)
				.map_err(|_| PortError::ImplementationSpecific)?),
			_ => Err(PortError::ImplementationSpecific),
		}
	}
}
