(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_balance" (func $seal_balance (param i32 i32)))
	(import "seal2" "call" (func $seal_call (param i32 i32 i64 i64 i32 i32 i32 i32 i32 i32) (result i32)))
	(import "seal2" "instantiate" (func $seal_instantiate
		(param i32 i64 i64 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32) (result i32)
	))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "deploy"))

	(func (export "call")
		(local $sp i32)
		(local $exit_code i32)

		;; Length of the buffer
		(i32.store (i32.const 20) (i32.const 32))

		;; Copy input to this contracts memory
		(call $seal_input (i32.const 24) (i32.const 20))

		;; Input data is the code hash of the contract to be deployed.
		(call $assert
			(i32.eq
				(i32.load (i32.const 20))
				(i32.const 32)
			)
		)

		;; Read current balance into local variable.
		(set_local $sp (i32.const 1024))

		;; Fail to deploy the contract since it returns a non-zero exit status.
		(set_local $exit_code
			(call $seal_instantiate
				(i32.const 24)	;; Pointer to the code hash.
				(i64.const 0)	;; How much ref_time weight to devote for the execution. 0 = all.
				(i64.const 0)	;; How much proof_size weight to devote for the execution. 0 = all.
				(i32.const 0xffffffff)	;; u32 max sentinel value: pass no deposit limit.
				(i32.const 0)	;; Pointer to the buffer with value to transfer
				(i32.const 9)	;; Pointer to input data buffer address
				(i32.const 7)	;; Length of input data buffer
				(i32.const 4294967295)	;; u32 max sentinel value: do not copy address
				(i32.const 0)	;; Length is ignored in this case
				(i32.const 4294967295) ;; u32 max sentinel value: do not copy output
				(i32.const 0)	;; Length is ignored in this case
				(i32.const 0)	;; salt_ptr
				(i32.const 0)	;; salt_le
			)
		)

		;; Check non-zero exit status.
		(call $assert
			(i32.eq (get_local $exit_code) (i32.const 2)) ;; ReturnCode::CalleeReverted
		)

		;; Fail to deploy the contract due to insufficient ref_time weight.
		(set_local $exit_code
			(call $seal_instantiate
				(i32.const 24)	;; Pointer to the code hash.
				(i64.const 1)	;; Supply too little ref_time weight
				(i64.const 0)	;; How much proof_size weight to devote for the execution. 0 = all.
				(i32.const 0xffffffff)	;; u32 max sentinel value: pass no deposit limit.
				(i32.const 0)	;; Pointer to the buffer with value to transfer
				(i32.const 8)	;; Pointer to input data buffer address
				(i32.const 8)	;; Length of input data buffer
				(i32.const 4294967295) ;; u32 max sentinel value: do not copy address
				(i32.const 0)	;; Length is ignored in this case
				(i32.const 4294967295) ;; u32 max sentinel value: do not copy output
				(i32.const 0)	;; Length is ignored in this case
				(i32.const 0)	;; salt_ptr
				(i32.const 0)	;; salt_le

			)
		)

		;; Check for special trap exit status.
		(call $assert
			(i32.eq (get_local $exit_code) (i32.const 1)) ;; ReturnCode::CalleeTrapped
		)

		;; Fail to deploy the contract due to insufficient ref_time weight.
		(set_local $exit_code
			(call $seal_instantiate
				(i32.const 24)	;; Pointer to the code hash.
				(i64.const 0)	;; How much ref_time weight to devote for the execution. 0 = all.
				(i64.const 1)	;; Supply too little proof_size weight
				(i32.const 0xffffffff)	;; u32 max sentinel value: pass no deposit limit.
				(i32.const 0)	;; Pointer to the buffer with value to transfer
				(i32.const 8)	;; Pointer to input data buffer address
				(i32.const 8)	;; Length of input data buffer
				(i32.const 4294967295)	;; u32 max sentinel value: do not copy address
				(i32.const 0)	;; Length is ignored in this case
				(i32.const 4294967295)	;; u32 max sentinel value: do not copy output
				(i32.const 0)	;; Length is ignored in this case
				(i32.const 0)	;; salt_ptr
				(i32.const 0)	;; salt_le

			)
		)

		;; Check for special trap exit status.
		(call $assert
			(i32.eq (get_local $exit_code) (i32.const 1)) ;; ReturnCode::CalleeTrapped
		)

		;; Length of the output buffer
		(i32.store
			(i32.sub (get_local $sp) (i32.const 4))
			(i32.const 256)
		)

		;; Deploy the contract successfully.
		(set_local $exit_code
			(call $seal_instantiate
				(i32.const 24)	;; Pointer to the code hash.
				(i64.const 0)	;; How much ref_time weight to devote for the execution. 0 = all.
				(i64.const 0)	;; How much proof_size weight to devote for the execution. 0 = all.
				(i32.const 0xffffffff)	;; u32 max sentinel value: pass no deposit limit.
				(i32.const 0)	;; Pointer to the buffer with value to transfer
				(i32.const 8)	;; Pointer to input data buffer address
				(i32.const 8)	;; Length of input data buffer
				(i32.const 16)	;; Pointer to the address output buffer
				(i32.sub (get_local $sp) (i32.const 4))	;; Pointer to the address buffer length
				(i32.const 4294967295)	;; u32 max sentinel value: do not copy output
				(i32.const 0)	;; Length is ignored in this case
				(i32.const 0)	;; salt_ptr
				(i32.const 0)	;; salt_le

			)
		)

		;; Check for success exit status.
		(call $assert
			(i32.eq (get_local $exit_code) (i32.const 0)) ;; ReturnCode::Success
		)

		;; Check that address has the expected length
		(call $assert
			(i32.eq (i32.load (i32.sub (get_local $sp) (i32.const 4))) (i32.const 32))
		)

		;; Zero out destination buffer of output
		(i32.store
			(i32.sub (get_local $sp) (i32.const 4))
			(i32.const 0)
		)

		;; Length of the output buffer
		(i32.store
			(i32.sub (get_local $sp) (i32.const 8))
			(i32.const 4)
		)

		;; Call the new contract and expect it to return failing exit code.
		(set_local $exit_code
			(call $seal_call
				(i32.const 0)	;; Set no flag
				(i32.const 16)	;; Pointer to "callee" address.
				(i64.const 0)	;; How much ref_time weight to devote for the execution. 0 = all.
				(i64.const 0)	;; How much proof_size weight to devote for the execution. 0 = all.
				(i32.const 0xffffffff)	;; u32 max sentinel value: pass no deposit limit.
				(i32.const 0)	;; Pointer to the buffer with value to transfer
				(i32.const 9)	;; Pointer to input data buffer address
				(i32.const 7)	;; Length of input data buffer
				(i32.sub (get_local $sp) (i32.const 4))	;; Ptr to output buffer
				(i32.sub (get_local $sp) (i32.const 8))	;; Ptr to output buffer len
			)
		)

		;; Check non-zero exit status.
		(call $assert
			(i32.eq (get_local $exit_code) (i32.const 2)) ;; ReturnCode::CalleeReverted
		)

		;; Check that output buffer contains the expected return data.
		(call $assert
			(i32.eq (i32.load (i32.sub (get_local $sp) (i32.const 8))) (i32.const 3))
		)
		(call $assert
			(i32.eq
				(i32.load (i32.sub (get_local $sp) (i32.const 4)))
				(i32.const 0x00776655)
			)
		)

		;; Fail to call the contract due to insufficient ref_time weight.
		(set_local $exit_code
			(call $seal_call
				(i32.const 0)	;; Set no flag
				(i32.const 16)	;; Pointer to "callee" address.
				(i64.const 1)	;; Supply too little ref_time weight
				(i64.const 0)	;; How much proof_size weight to devote for the execution. 0 = all.
				(i32.const 0xffffffff)	;; u32 max sentinel value: pass no deposit limit.
				(i32.const 0)	;; Pointer to the buffer with value to transfer
				(i32.const 8)	;; Pointer to input data buffer address
				(i32.const 8)	;; Length of input data buffer
				(i32.const 4294967295)	;; u32 max sentinel value: do not copy output
				(i32.const 0)	;; Length is ignored in this cas
			)
		)

		;; Check for special trap exit status.
		(call $assert
			(i32.eq (get_local $exit_code) (i32.const 1)) ;; ReturnCode::CalleeTrapped
		)

		;; Fail to call the contract due to insufficient proof_size weight.
		(set_local $exit_code
			(call $seal_call
				(i32.const 0)	;; Set no flag
				(i32.const 16)	;; Pointer to "callee" address.
				(i64.const 0)	;; How much ref_time weight to devote for the execution. 0 = all.
				(i64.const 1)	;; Supply too little proof_size weight
				(i32.const 0xffffffff)	;; u32 max sentinel value: pass no deposit limit.
				(i32.const 0)	;; Pointer to the buffer with value to transfer
				(i32.const 8)	;; Pointer to input data buffer address
				(i32.const 8)	;; Length of input data buffer
				(i32.const 4294967295)	;; u32 max sentinel value: do not copy output
				(i32.const 0)	;; Length is ignored in this cas
			)
		)

		;; Check for special trap exit status.
		(call $assert
			(i32.eq (get_local $exit_code) (i32.const 1)) ;; ReturnCode::CalleeTrapped
		)

		;; Zero out destination buffer of output
		(i32.store
			(i32.sub (get_local $sp) (i32.const 4))
			(i32.const 0)
		)

		;; Length of the output buffer
		(i32.store
			(i32.sub (get_local $sp) (i32.const 8))
			(i32.const 4)
		)

		;; Call the contract successfully.
		(set_local $exit_code
			(call $seal_call
				(i32.const 0)	;; Set no flag
				(i32.const 16)	;; Pointer to "callee" address.
				(i64.const 0)	;; How much ref_time weight to devote for the execution. 0 = all.
				(i64.const 0)	;; How much proof_size weight to devote for the execution. 0 = all.
				(i32.const 0xffffffff)	;; u32 max sentinel value: pass no deposit limit.
				(i32.const 0)	;; Pointer to the buffer with value to transfer
				(i32.const 8)	;; Pointer to input data buffer address
				(i32.const 8)	;; Length of input data buffer
				(i32.sub (get_local $sp) (i32.const 4))	;; Ptr to output buffer
				(i32.sub (get_local $sp) (i32.const 8))	;; Ptr to output buffer len
			)
		)

		;; Check for success exit status.
		(call $assert
			(i32.eq (get_local $exit_code) (i32.const 0)) ;; ReturnCode::Success
		)

		;; Check that the output buffer contains the expected return data.
		(call $assert
			(i32.eq (i32.load (i32.sub (get_local $sp) (i32.const 8))) (i32.const 4))
		)
		(call $assert
			(i32.eq
				(i32.load (i32.sub (get_local $sp) (i32.const 4)))
				(i32.const 0x77665544)
			)
		)
	)

	(data (i32.const 0) "\00\80")		;; The value to transfer on instantiation and calls.
										;; Chosen to be greater than existential deposit.
	(data (i32.const 8) "\00\01\22\33\44\55\66\77")		;; The input data to instantiations and calls.
)
