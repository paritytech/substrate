;; Stores a value of the passed size in constructor.
(module
	(import "seal0" "seal_set_storage" (func $seal_set_storage (param i32 i32 i32)))
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "env" "memory" (memory 16 16))

	;; [0, 32) storage key
	(data (i32.const 0) "\01")

	;; [32, 36) buffer where input is copied (expected size of storage item)

	;; [36, 40) size of the input buffer
	(data (i32.const 36) "\04")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "deploy")
		(call $seal_input (i32.const 32) (i32.const 36))

		;; assert input size == 4
		(call $assert
			(i32.eq
				(i32.load (i32.const 36))
				(i32.const 4)
			)
		)

		;; place a value in storage, the size of which is specified by the call input.
		;; we don't care about the contents of the storage item
		(call $seal_set_storage
			(i32.const 0)		;; Pointer to storage key
			(i32.const 0)		;; Pointer to value
			(i32.load (i32.const 32))	;; Size of value
		)
	)

	(func (export "call"))
)
