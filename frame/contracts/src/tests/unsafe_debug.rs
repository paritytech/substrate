#![cfg(feature = "unsafe-debug")]

use super::*;
use crate::unsafe_debug::{ExecutionObserver, ExportedFunction};
use frame_support::traits::Currency;
use pallet_contracts_primitives::ExecReturnValue;
use pretty_assertions::assert_eq;
use std::cell::RefCell;

#[derive(Clone, PartialEq, Eq, Debug)]
struct DebugFrame {
	code_hash: CodeHash<Test>,
	call: ExportedFunction,
	input: Vec<u8>,
	result: Option<Vec<u8>>,
}

thread_local! {
	static DEBUG_EXECUTION_TRACE: RefCell<Vec<DebugFrame>> = RefCell::new(Vec::new());
}

pub struct TestDebugger;

impl ExecutionObserver<CodeHash<Test>> for TestDebugger {
	fn before_call(code_hash: &CodeHash<Test>, entry_point: ExportedFunction, input_data: &[u8]) {
		DEBUG_EXECUTION_TRACE.with(|d| {
			d.borrow_mut().push(DebugFrame {
				code_hash: code_hash.clone(),
				call: entry_point,
				input: input_data.to_vec(),
				result: None,
			})
		});
	}

	fn after_call(
		code_hash: &CodeHash<Test>,
		entry_point: ExportedFunction,
		input_data: Vec<u8>,
		output: &ExecReturnValue,
	) {
		DEBUG_EXECUTION_TRACE.with(|d| {
			d.borrow_mut().push(DebugFrame {
				code_hash: code_hash.clone(),
				call: entry_point,
				input: input_data,
				result: Some(output.data.clone()),
			})
		});
	}
}

#[test]
fn unsafe_debugging_works() {
	let (wasm_caller, code_hash_caller) = compile_module::<Test>("call").unwrap();
	let (wasm_callee, code_hash_callee) = compile_module::<Test>("store_call").unwrap();

	fn current_stack() -> Vec<DebugFrame> {
		DEBUG_EXECUTION_TRACE.with(|stack| stack.borrow().clone())
	}

	fn deploy(wasm: Vec<u8>) -> AccountId32 {
		Contracts::bare_instantiate(
			ALICE,
			0,
			GAS_LIMIT,
			None,
			Code::Upload(wasm),
			vec![],
			vec![],
			DebugInfo::Skip,
			CollectEvents::Skip,
		)
		.result
		.unwrap()
		.account_id
	}

	fn constructor_frame(hash: CodeHash<Test>, after: bool) -> DebugFrame {
		DebugFrame {
			code_hash: hash,
			call: ExportedFunction::Constructor,
			input: vec![],
			result: if after { Some(vec![]) } else { None },
		}
	}

	fn call_frame(hash: CodeHash<Test>, args: Vec<u8>, after: bool) -> DebugFrame {
		DebugFrame {
			code_hash: hash,
			call: ExportedFunction::Call,
			input: args,
			result: if after { Some(vec![]) } else { None },
		}
	}

	ExtBuilder::default().existential_deposit(200).build().execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 1_000_000);

		assert_eq!(current_stack(), vec![]);

		let addr_caller = deploy(wasm_caller);
		let addr_callee = deploy(wasm_callee);

		assert_eq!(
			current_stack(),
			vec![
				constructor_frame(code_hash_caller, false),
				constructor_frame(code_hash_caller, true),
				constructor_frame(code_hash_callee, false),
				constructor_frame(code_hash_callee, true),
			]
		);

		let main_args = (100u32, &addr_callee).encode();
		let inner_args = (100u32).encode();

		assert_ok!(Contracts::call(
			RuntimeOrigin::signed(ALICE),
			addr_caller,
			0,
			GAS_LIMIT,
			None,
			main_args.clone()
		));

		let stack_top = current_stack()[4..].to_vec();
		assert_eq!(
			stack_top,
			vec![
				call_frame(code_hash_caller, main_args.clone(), false),
				call_frame(code_hash_callee, inner_args.clone(), false),
				call_frame(code_hash_callee, inner_args, true),
				call_frame(code_hash_caller, main_args, true),
			]
		);
	});
}
