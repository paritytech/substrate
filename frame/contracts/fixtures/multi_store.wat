;; Does two stores to two seperate storage items
;; Expects (len0, len1) as input.
(module
	(import "seal0" "seal_set_storage" (func $seal_set_storage (param i32 i32 i32)))
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "env" "memory" (memory 16 16))

	;; [0, 32) storage key 0
	(data (i32.const 0) "\01")

	;; [32, 64) storage key 1
	(data (i32.const 32) "\02")

	;; [64, 72) buffer where input is copied (expected sizes of storage items)

	;; [72, 76) size of the input buffer
	(data (i32.const 72) "\08")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		(call $seal_input (i32.const 64) (i32.const 72))

		;; assert input size == 8
		(call $assert
			(i32.eq
				(i32.load (i32.const 72))
				(i32.const 8)
			)
		)

		;; place a values in storage sizes are specified in the input buffer
		;; we don't care about the contents of the storage item
		(call $seal_set_storage
			(i32.const 0)		;; Pointer to storage key
			(i32.const 0)		;; Pointer to value
			(i32.load (i32.const 64))	;; Size of value
		)
		(call $seal_set_storage
			(i32.const 32)		;; Pointer to storage key
			(i32.const 0)		;; Pointer to value
			(i32.load (i32.const 68))	;; Size of value
		)
	)

	(func (export "deploy"))
)
