use super::*;
frame_benchmarking::benchmarks! {
	join {}: {}
	claim_payout {}: {}
	unbond_other {}: {}
	pool_withdraw_unbonded {}: {}
	withdraw_unbonded_other {}: {}
	create {}: {}
	nominate {}: {}
}
