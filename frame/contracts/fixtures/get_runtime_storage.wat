(module
	(import "env" "ext_get_runtime_storage"
		(func $ext_get_runtime_storage (param i32 i32) (result i32))
	)
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_read" (func $ext_scratch_read (param i32 i32 i32)))
	(import "env" "ext_scratch_write" (func $ext_scratch_write (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "deploy"))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func $call (export "call")
		;; Load runtime storage for the first key and assert that it exists.
		(call $assert
			(i32.eq
				(call $ext_get_runtime_storage
					(i32.const 16)
					(i32.const 4)
				)
				(i32.const 0)
			)
		)

		;; assert $ext_scratch_size == 4
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 4)
			)
		)

		;; copy contents of the scratch buffer into the contract's memory.
		(call $ext_scratch_read
			(i32.const 4)		;; Pointer in memory to the place where to copy.
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 4)		;; Count of bytes to copy.
		)

		;; assert that contents of the buffer is equal to the i32 value of 0x14144020.
		(call $assert
			(i32.eq
				(i32.load
					(i32.const 4)
				)
				(i32.const 0x14144020)
			)
		)

		;; Load the second key and assert that it doesn't exist.
		(call $assert
			(i32.eq
				(call $ext_get_runtime_storage
					(i32.const 20)
					(i32.const 4)
				)
				(i32.const 1)
			)
		)
	)

	;; The first key, 4 bytes long.
	(data (i32.const 16) "\01\02\03\04")
	;; The second key, 4 bytes long.
	(data (i32.const 20) "\02\03\04\05")
)
