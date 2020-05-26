(module
	(import "env" "ext_get_storage" (func $ext_get_storage (param i32) (result i32)))
	(import "env" "ext_set_storage" (func $ext_set_storage (param i32 i32 i32)))
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_read" (func $ext_scratch_read (param i32 i32 i32)))
	(import "env" "memory" (memory 16 16))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; assert $ext_scratch_size == 8
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 4)
			)
		)

		;; copy contents of the scratch buffer into the contract's memory.
		(call $ext_scratch_read
			(i32.const 32)		;; Pointer in memory to the place where to copy.
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 4)		;; Count of bytes to copy.
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
				)
				(i32.const 0)
			)
		)

		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.load (i32.const 32))
			)
		)
	)

	(func (export "deploy"))

	(data (i32.const 0) "\01")	;; Storage key (32 B)
)
