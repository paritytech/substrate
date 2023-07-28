;; Just delegate call into the passed code hash and assert success.
(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_delegate_call" (func $seal_delegate_call (param i32 i32 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 3 3))

	;; [0, 32) buffer where input is copied

	;; [32, 36) size of the input buffer
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; Reading "callee" code_hash
		(call $seal_input (i32.const 0) (i32.const 32))

		;; assert input size == 32
		(call $assert
			(i32.eq
				(i32.load (i32.const 32))
				(i32.const 32)
			)
		)

		;; Delegate call into passed code hash
		(call $assert
			(i32.eq
				(call $seal_delegate_call
					(i32.const 0)	;; Set no call flags
					(i32.const 0)	;; Pointer to "callee" code_hash.
					(i32.const 0)	;; Input is ignored
					(i32.const 0)	;; Length of the input
					(i32.const 4294967295)	;; u32 max sentinel value: do not copy output
					(i32.const 0)	;; Length is ignored in this case
				)
				(i32.const 0)
			)
		)
	)

	(func (export "deploy"))
)
