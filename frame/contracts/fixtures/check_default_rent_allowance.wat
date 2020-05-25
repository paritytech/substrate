(module
	(import "env" "ext_rent_allowance" (func $ext_rent_allowance))
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_read" (func $ext_scratch_read (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call"))

	(func (export "deploy")
		;; fill the scratch buffer with the rent allowance.
		(call $ext_rent_allowance)

		;; assert $ext_scratch_size == 8
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 8)
			)
		)

		;; copy contents of the scratch buffer into the contract's memory.
		(call $ext_scratch_read
			(i32.const 8)		;; Pointer in memory to the place where to copy.
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 8)		;; Count of bytes to copy.
		)

		;; assert that contents of the buffer is equal to <BalanceOf<T>>::max_value().
		(call $assert
			(i64.eq
				(i64.load
					(i32.const 8)
				)
				(i64.const 0xFFFFFFFFFFFFFFFF)
			)
		)
	)
)
