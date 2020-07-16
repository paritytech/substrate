(module
	(import "env" "ext_get_storage" (func $ext_get_storage (param i32 i32 i32) (result i32)))
	(import "env" "ext_set_storage" (func $ext_set_storage (param i32 i32 i32)))
	(import "env" "ext_input" (func $ext_input (param i32 i32)))
	(import "env" "memory" (memory 16 16))

	;; [0, 32) storage key
	(data (i32.const 0) "\01")

	;; [32, 36) buffer where input is copied (expected size of storage item)

	;; [36, 40) size of the input buffer
	(data (i32.const 36) "\04")

	;; [40, 44) size of buffer for ext_get_storage set to max
	(data (i32.const 40) "\FF\FF\FF\FF")

	;; [44, inf) ext_get_storage buffer

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		(call $ext_input (i32.const 32) (i32.const 36))

		;; assert input size == 4
		(call $assert
			(i32.eq
				(i32.load (i32.const 36))
				(i32.const 4)
			)
		)

		;; place a garbage value in storage, the size of which is specified by the call input.
		(call $ext_set_storage
			(i32.const 0)		;; Pointer to storage key
			(i32.const 0)		;; Pointer to value
			(i32.load (i32.const 32))	;; Size of value
		)

		(call $assert
			(i32.eq
				(call $ext_get_storage
					(i32.const 0)		;; Pointer to storage key
					(i32.const 44)		;; buffer where to copy result
					(i32.const 40)		;; pointer to size of buffer
				)
				(i32.const 0)
			)
		)

		(call $assert
			(i32.eq
				(i32.load (i32.const 40))
				(i32.load (i32.const 32))
			)
		)
	)

	(func (export "deploy"))

)
