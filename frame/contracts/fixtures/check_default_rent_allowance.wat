(module
	(import "seal0" "seal_rent_allowance" (func $seal_rent_allowance (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 8) reserved for $seal_rent_allowance output

	;; [8, 16) length of the buffer
	(data (i32.const 8) "\08")

	;; [16, inf) zero initialized

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
		;; fill the buffer with the rent allowance.
		(call $seal_rent_allowance (i32.const 0) (i32.const 8))

		;; assert len == 8
		(call $assert
			(i32.eq
				(i32.load (i32.const 8))
				(i32.const 8)
			)
		)

		;; assert that contents of the buffer is equal to <BalanceOf<T>>::max_value().
		(call $assert
			(i64.eq
				(i64.load (i32.const 0))
				(i64.const 0xFFFFFFFFFFFFFFFF)
			)
		)
	)
)
