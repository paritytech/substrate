;; This fixture recursively tests if reentrance_count returns correct reentrant count value when
;; using seal_delegate_call to make caller contract delegate call to itself
(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_set_storage" (func $seal_set_storage (param i32 i32 i32)))
	(import "seal0" "seal_delegate_call" (func $seal_delegate_call (param i32 i32 i32 i32 i32 i32) (result i32)))
	(import "__unstable__" "reentrance_count" (func $reentrance_count (result i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 32) buffer where code hash is copied

	;; [32, 36) buffer for the call stack height

	;; [36, 40) size of the input buffer
	(data (i32.const 36) "\24")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)
	(func (export "call")
		(local $callstack_height i32)
		(local $delegate_call_exit_code i32)

		;; Reading input
		(call $seal_input (i32.const 0) (i32.const 36))

		;; reading passed callstack height
		(set_local $callstack_height (i32.load (i32.const 32)))

		;; incrementing callstack height
		(i32.store (i32.const 32) (i32.add (i32.load (i32.const 32)) (i32.const 1)))

		;; reentrance count stays 0
		(call $assert
			(i32.eq (call $reentrance_count) (i32.const 0))
		)

		(i32.eq (get_local $callstack_height) (i32.const 5))
		(if
			(then) ;; exit recursion case
			(else
				;; Call to itself
				(set_local $delegate_call_exit_code
					(call $seal_delegate_call
						(i32.const 0)	;; Set no call flags
						(i32.const 0)	;; Pointer to "callee" code_hash.
						(i32.const 0)	;; Pointer to the input data
						(i32.const 36)	;; Length of the input
						(i32.const 4294967295)	;; u32 max sentinel value: do not copy output
						(i32.const 0)	;; Length is ignored in this case
					)
				)

				(call $assert
					(i32.eq (get_local $delegate_call_exit_code) (i32.const 0))
				)
			)
		)

		(call $assert
			(i32.le_s (get_local $callstack_height) (i32.const 5))
		)
	)

	(func (export "deploy"))
)