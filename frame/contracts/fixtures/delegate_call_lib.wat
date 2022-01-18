(module
	(import "seal0" "seal_set_storage" (func $seal_set_storage (param i32 i32 i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 32) storage key
	(data (i32.const 0) "\01")

	;; size of the value to put in storage
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
		;; place a value in storage
		(call $seal_set_storage
			(i32.const 0)		;; Pointer to storage key
			(i32.const 0)		;; Pointer to value
			(i32.load (i32.const 32))	;; Size of value
		)

		;; exit with success and take transfer return code to the output buffer
		(call $seal_return (i32.const 0) (i32.const 0) (i32.const 4))
	)

	(func (export "deploy"))
)
