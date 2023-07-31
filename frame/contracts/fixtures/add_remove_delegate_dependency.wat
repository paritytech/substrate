;; This contract tests the behavior of adding / removing delegate_dependencies when delegate calling into a contract.
(module
	(import "seal0" "add_delegate_dependency" (func $add_delegate_dependency (param i32)))
	(import "seal0" "remove_delegate_dependency" (func $remove_delegate_dependency (param i32)))
	(import "seal0" "input" (func $input (param i32 i32)))
	(import "seal1" "terminate" (func $terminate (param i32)))
	(import "seal0" "delegate_call" (func $delegate_call (param i32 i32 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))

	;; [100, 132) Address of Alice
	(data (i32.const 100)
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
	)

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	;; This function loads input data and performs the action specified.
	;; The first 4 bytes of the input specify the action to perform.
	;; The next 32 bytes specify the code hash to use when calling add_delegate_dependency or remove_delegate_dependency.
	;; Actions are:
	;; 1: call add_delegate_dependency
	;; 2: call remove_delegate_dependency.
	;; 3: call terminate.
	;; Any other value is a no-op.
	(func $load_input
		(local $action i32)
		(local $code_hash_ptr i32)

	    ;; Store available input size at offset 0.
        (i32.store (i32.const 0) (i32.const 512))

		;; Read input data.
		(call $input (i32.const 4) (i32.const 0))

		;; Input data layout.
		;; [0..4) - size of the call
		;; [4..8) - action to perform
		;; [8..42) - code hash of the callee
		(set_local $action (i32.load (i32.const 4)))
		(set_local $code_hash_ptr (i32.const 8))

		;; Assert input size == 36 (4 for action + 32 for code_hash).
		(call $assert
			(i32.eq
				(i32.load (i32.const 0))
				(i32.const 36)
			)
		)

		;; Call add_delegate_dependency when action == 1.
		(if (i32.eq (get_local $action) (i32.const 1))
		    (then
				(call $add_delegate_dependency (get_local $code_hash_ptr))
			)
			(else)
		)

		;; Call remove_delegate_dependency when action == 2.
		(if (i32.eq (get_local $action) (i32.const 2))
		    (then
				(call $remove_delegate_dependency
					(get_local $code_hash_ptr)
				)
			)
			(else)
		)

		;; Call terminate when action == 3.
		(if (i32.eq (get_local $action) (i32.const 3))
		    (then
				(call $terminate
					(i32.const 100)	;; Pointer to beneficiary address
				)
				(unreachable) ;; terminate never returns
			)
			(else)
		)
	)

	(func (export "deploy")
		(call $load_input)
	)

	(func (export "call")
		(call $load_input)

		;; Delegate call into passed code hash.
		(call $assert
			(i32.eq
				(call $delegate_call
					(i32.const 0)	;; Set no call flags.
					(i32.const 8)	;; Pointer to "callee" code_hash.
					(i32.const 0)	;; Input is ignored.
					(i32.const 0)	;; Length of the input.
					(i32.const 4294967295)	;; u32 max sentinel value: do not copy output.
					(i32.const 0)	;; Length is ignored in this case.
				)
				(i32.const 0)
			)
		)
	)

)
