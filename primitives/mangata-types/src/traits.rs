
pub trait GetMaintenanceStatusTrait {
	fn is_maintenance() -> bool;

	fn is_upgradable() -> bool;
}
