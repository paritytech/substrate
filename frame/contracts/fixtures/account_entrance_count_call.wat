(module
	(import "__unstable__" "seal_account_entrance_count" (func $seal_account_entrance_count (result i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)
	(func (export "call")
		(local $entrance_count i32)

		(set_local $entrance_count
			(call $seal_account_entrance_count)
		)

		;; assert account_entrance_count == 1
		(call $assert
		   	(i32.eq (get_local $account_entrance_count) (i32.const 1))
		)
	)

	(func (export "deploy"))

)
