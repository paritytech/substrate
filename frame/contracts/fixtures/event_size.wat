(module
	(import "seal0" "seal_deposit_event" (func $seal_deposit_event (param i32 i32 i32 i32)))
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "env" "memory" (memory 16 16))

	;; [0, 4) size of the input buffer
	(data (i32.const 0) "\04")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		(call $seal_input (i32.const 4) (i32.const 0))

		;; assert input size == 4
		(call $assert
			(i32.eq
				(i32.load (i32.const 0))
				(i32.const 4)
			)
		)

		;; place a garbage value in storage, the size of which is specified by the call input.
		(call $seal_deposit_event
			(i32.const 0) ;; topics_ptr
			(i32.const 0) ;; topics_len
			(i32.const 0) ;; data_ptr
			(i32.load (i32.const 4)) ;; data_len
		)
	)

	(func (export "deploy"))
)
