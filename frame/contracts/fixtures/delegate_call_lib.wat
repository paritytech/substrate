(module
	(import "seal0" "seal_set_storage" (func $seal_set_storage (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 32) storage key
	(data (i32.const 0) "\01")

	(func (export "call")
		;; place a value in storage
		(call $seal_set_storage
			(i32.const 0)		;; Pointer to storage key
			(i32.const 0)		;; Pointer to value
			(i32.const 32)		;; Size of value
		)
	)

	(func (export "deploy"))
)
