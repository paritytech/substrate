;; This fixture tests if seal_account_entrance_count works as expected
;; testing it with 2 different addresses
(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_caller" (func $seal_caller (param i32 i32)))
	(import "__unstable__" "seal_account_entrance_count" (func $seal_account_entrance_count (param i32) (result i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 32) buffer where input is copied
	;; [32, 64) buffer where caller is copied

	;; [64, 68) size of the input buffer
	(data (i32.const 64) "\20")
	;; [68, 72) size of the caller buffer
	(data (i32.const 68) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		(local $account_entrance_count i32)

		;; Reading "callee" contract address
		(call $seal_input (i32.const 0) (i32.const 64))

		;; Reading "caller" contract address
		(call $seal_caller (i32.const 32) (i32.const 68))

		(i32.eq
		    (i32.load (i32.const 0))
		    (i32.load (i32.const 32))
		)
		(if
		    (then
                ;; If the caller is the same as the callee then seal_account_entrance_count should be 2
                (call $assert
                    (i32.eq
                        (call $seal_account_entrance_count (i32.const 0))
                        (i32.const 2)
                    )
                )
            )
		    (else
                ;; If the caller is different from the callee then seal_account_entrance_count should be 1
                (call $assert
                    (i32.eq
                        (call $seal_account_entrance_count (i32.const 0))
                        (i32.const 1)
                    )
                )
            )
		)
	)

	(func (export "deploy"))

)
