;; This module stores a KV pair into the storage
(module
	(import "seal0" "seal_set_storage" (func $seal_set_storage (param i32 i32 i32)))
	(import "env" "memory" (memory 16 16))

	(func (export "call")
	)
	(func (export "deploy")
		(call $seal_set_storage
			(i32.const 0)				;; Pointer to storage key
			(i32.const 0)				;; Pointer to value
			(i32.load (i32.const 0))	;; Size of value
		)
	)
)
