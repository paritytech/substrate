(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "seal0" "seal_set_code_hash" (func $seal_set_code_hash (param i32) (result i32)))

	(import "env" "memory" (memory 1 1))

	;; [0, 32) here we store input

	;; [32, 36) input size
	(data (i32.const 32) "\20")

	;; [36, 40) return value
	(data (i32.const 36) "\01")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		(local $exit_code i32)

		(call $seal_input (i32.const 0) (i32.const 32))

		(set_local $exit_code
			(call $seal_set_code_hash (i32.const 0)) ;; Pointer to the input data.
		)
		(call $assert
			(i32.eq (get_local $exit_code) (i32.const 0)) ;; ReturnCode::Success
		)

		;; we return 1 after setting new code_hash
		;; next `call` will NOT return this value, because contract code has been changed
		(call $seal_return (i32.const 0) (i32.const 36) (i32.const 4))
	)

	(func (export "deploy"))
)
