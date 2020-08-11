(module
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_read" (func $ext_scratch_read (param i32 i32 i32)))
	(import "env" "ext_balance" (func $ext_balance))
	(import "env" "ext_call" (func $ext_call (param i32 i32 i64 i32 i32 i32 i32) (result i32)))
	(import "env" "ext_instantiate" (func $ext_instantiate (param i32 i32 i64 i32 i32 i32 i32) (result i32)))
	(import "env" "ext_println" (func $ext_println (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func $current_balance (param $sp i32) (result i64)
		(call $ext_balance)
		(call $assert
			(i32.eq (call $ext_scratch_size) (i32.const 8))
		)
		(call $ext_scratch_read
			(i32.sub (get_local $sp) (i32.const 8))
			(i32.const 0)
			(i32.const 8)
		)
		(i64.load (i32.sub (get_local $sp) (i32.const 8)))
	)

	(func (export "deploy"))

	(func (export "call")
		(local $sp i32)
		(local $exit_code i32)
		(local $balance i64)

		;; Input data is the code hash of the contract to be deployed.
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 32)
			)
		)

		;; Copy code hash from scratch buffer into this contract's memory.
		(call $ext_scratch_read
			(i32.const 24)		;; The pointer where to store the scratch buffer contents,
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 32)		;; Count of bytes to copy.
		)

		;; Read current balance into local variable.
		(set_local $sp (i32.const 1024))
		(set_local $balance
			(call $current_balance (get_local $sp))
		)

		;; Fail to deploy the contract since it returns a non-zero exit status.
		(set_local $exit_code
			(call $ext_instantiate
				(i32.const 24)	;; Pointer to the code hash.
				(i32.const 32)	;; Length of the code hash.
				(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
				(i32.const 0)	;; Pointer to the buffer with value to transfer
				(i32.const 8)	;; Length of the buffer with value to transfer.
				(i32.const 9)	;; Pointer to input data buffer address
				(i32.const 7)	;; Length of input data buffer
			)
		)

		;; Check non-zero exit status.
		(call $assert
			(i32.eq (get_local $exit_code) (i32.const 0x11))
		)

		;; Check that scratch buffer is empty since contract instantiation failed.
		(call $assert
			(i32.eq (call $ext_scratch_size) (i32.const 0))
		)

		;; Check that balance has not changed.
		(call $assert
			(i64.eq (get_local $balance) (call $current_balance (get_local $sp)))
		)

		;; Fail to deploy the contract due to insufficient gas.
		(set_local $exit_code
			(call $ext_instantiate
				(i32.const 24)	;; Pointer to the code hash.
				(i32.const 32)	;; Length of the code hash.
				(i64.const 200)	;; How much gas to devote for the execution.
				(i32.const 0)	;; Pointer to the buffer with value to transfer
				(i32.const 8)	;; Length of the buffer with value to transfer.
				(i32.const 8)	;; Pointer to input data buffer address
				(i32.const 8)	;; Length of input data buffer
			)
		)

		;; Check for special trap exit status.
		(call $assert
			(i32.eq (get_local $exit_code) (i32.const 0x0100))
		)

		;; Check that scratch buffer is empty since contract instantiation failed.
		(call $assert
			(i32.eq (call $ext_scratch_size) (i32.const 0))
		)

		;; Check that balance has not changed.
		(call $assert
			(i64.eq (get_local $balance) (call $current_balance (get_local $sp)))
		)

		;; Deploy the contract successfully.
		(set_local $exit_code
			(call $ext_instantiate
				(i32.const 24)	;; Pointer to the code hash.
				(i32.const 32)	;; Length of the code hash.
				(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
				(i32.const 0)	;; Pointer to the buffer with value to transfer
				(i32.const 8)	;; Length of the buffer with value to transfer.
				(i32.const 8)	;; Pointer to input data buffer address
				(i32.const 8)	;; Length of input data buffer
			)
		)

		;; Check for success exit status.
		(call $assert
			(i32.eq (get_local $exit_code) (i32.const 0x00))
		)

		;; Check that scratch buffer contains the address of the new contract.
		(call $assert
			(i32.eq (call $ext_scratch_size) (i32.const 8))
		)

		;; Copy contract address from scratch buffer into this contract's memory.
		(call $ext_scratch_read
			(i32.const 16)		;; The pointer where to store the scratch buffer contents,
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 8)		;; Count of bytes to copy.
		)

		;; Check that balance has been deducted.
		(set_local $balance
			(i64.sub (get_local $balance) (i64.load (i32.const 0)))
		)
		(call $assert
			(i64.eq (get_local $balance) (call $current_balance (get_local $sp)))
		)

		;; Call the new contract and expect it to return failing exit code.
		(set_local $exit_code
			(call $ext_call
				(i32.const 16)	;; Pointer to "callee" address.
				(i32.const 8)	;; Length of "callee" address.
				(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
				(i32.const 0)	;; Pointer to the buffer with value to transfer
				(i32.const 8)	;; Length of the buffer with value to transfer.
				(i32.const 9)	;; Pointer to input data buffer address
				(i32.const 7)	;; Length of input data buffer
			)
		)

		;; Check non-zero exit status.
		(call $assert
			(i32.eq (get_local $exit_code) (i32.const 0x11))
		)

		;; Check that scratch buffer contains the expected return data.
		(call $assert
			(i32.eq (call $ext_scratch_size) (i32.const 3))
		)
		(i32.store
			(i32.sub (get_local $sp) (i32.const 4))
			(i32.const 0)
		)
		(call $ext_scratch_read
			(i32.sub (get_local $sp) (i32.const 4))
			(i32.const 0)
			(i32.const 3)
		)
		(call $assert
			(i32.eq
				(i32.load (i32.sub (get_local $sp) (i32.const 4)))
				(i32.const 0x00776655)
			)
		)

		;; Check that balance has not changed.
		(call $assert
			(i64.eq (get_local $balance) (call $current_balance (get_local $sp)))
		)

		;; Fail to call the contract due to insufficient gas.
		(set_local $exit_code
			(call $ext_call
				(i32.const 16)	;; Pointer to "callee" address.
				(i32.const 8)	;; Length of "callee" address.
				(i64.const 100)	;; How much gas to devote for the execution.
				(i32.const 0)	;; Pointer to the buffer with value to transfer
				(i32.const 8)	;; Length of the buffer with value to transfer.
				(i32.const 8)	;; Pointer to input data buffer address
				(i32.const 8)	;; Length of input data buffer
			)
		)

		;; Check for special trap exit status.
		(call $assert
			(i32.eq (get_local $exit_code) (i32.const 0x0100))
		)

		;; Check that scratch buffer is empty since call trapped.
		(call $assert
			(i32.eq (call $ext_scratch_size) (i32.const 0))
		)

		;; Check that balance has not changed.
		(call $assert
			(i64.eq (get_local $balance) (call $current_balance (get_local $sp)))
		)

		;; Call the contract successfully.
		(set_local $exit_code
			(call $ext_call
				(i32.const 16)	;; Pointer to "callee" address.
				(i32.const 8)	;; Length of "callee" address.
				(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
				(i32.const 0)	;; Pointer to the buffer with value to transfer
				(i32.const 8)	;; Length of the buffer with value to transfer.
				(i32.const 8)	;; Pointer to input data buffer address
				(i32.const 8)	;; Length of input data buffer
			)
		)

		;; Check for success exit status.
		(call $assert
			(i32.eq (get_local $exit_code) (i32.const 0x00))
		)

		;; Check that scratch buffer contains the expected return data.
		(call $assert
			(i32.eq (call $ext_scratch_size) (i32.const 4))
		)
		(i32.store
			(i32.sub (get_local $sp) (i32.const 4))
			(i32.const 0)
		)
		(call $ext_scratch_read
			(i32.sub (get_local $sp) (i32.const 4))
			(i32.const 0)
			(i32.const 4)
		)
		(call $assert
			(i32.eq
				(i32.load (i32.sub (get_local $sp) (i32.const 4)))
				(i32.const 0x77665544)
			)
		)

		;; Check that balance has been deducted.
		(set_local $balance
			(i64.sub (get_local $balance) (i64.load (i32.const 0)))
		)
		(call $assert
			(i64.eq (get_local $balance) (call $current_balance (get_local $sp)))
		)
	)

	(data (i32.const 0) "\00\80")		;; The value to transfer on instantiation and calls.
										;; Chosen to be greater than existential deposit.
	(data (i32.const 8) "\00\11\22\33\44\55\66\77")		;; The input data to instantiations and calls.
)
