;; This fixture tests if seal_account_entrance_count works as expected
;; testing it with 2 different addresses
(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_caller" (func $seal_caller (param i32 i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
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
		;; Reading input address
		(call $seal_input (i32.const 0) (i32.const 32))

		(i32.store
		    (i32.const 36)
            (call $seal_account_entrance_count (i32.const 0))
		)

		(call $seal_return (i32.const 0) (i32.const 36) (i32.const 4))
	)

	(func (export "deploy"))

)
