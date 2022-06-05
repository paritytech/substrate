(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "__unstable__" "seal_account_entrance_count" (func $seal_account_entrance_count (param i32) (result i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 32) buffer where input is copied

	;; [32, 36) size of the input buffer
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)
	(func (export "call")
		(local $account_entrance_count i32)

	    ;; Reading "callee" contract address (which is the address of the caller)
	    (call $seal_input (i32.const 0) (i32.const 32))

		(set_local $account_entrance_count
			(call $seal_account_entrance_count (i32.const 0))
		)

		;; assert account_entrance_count == 1
		(call $assert
		   	(i32.eq (get_local $account_entrance_count) (i32.const 1))
		)
	)

	(func (export "deploy"))

)
