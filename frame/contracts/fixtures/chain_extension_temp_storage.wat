;; Call chain extension two times with the specified func_ids
;; It then calls itself once
(module
	(import "seal0" "seal_call_chain_extension"
		(func $seal_call_chain_extension (param i32 i32 i32 i32 i32) (result i32))
	)
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_address" (func $seal_address (param i32 i32)))
	(import "seal1" "seal_call" (func $seal_call (param i32 i32 i64 i32 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 16 16))

	(func $assert (param i32)
		(block $ok
			(br_if $ok (get_local 0))
			(unreachable)
		)
	)

	;; [0, 4) len of input buffer: 8 byte (func_ids) + 1byte (stop_recurse)
	(data (i32.const 0) "\09")

	;; [4, 16) buffer for input

	;; [16, 48] buffer for self address

	;; [48, 52] len of self address buffer
	(data (i32.const 48) "\20")

	(func (export "deploy"))

	(func (export "call")
		;; input: (func_id1: i32, func_id2: i32, stop_recurse: i8)
		(call $seal_input (i32.const 4) (i32.const 0))

		(call $seal_call_chain_extension
			(i32.load (i32.const 4))	;; id
			(i32.const 0)				;; input_ptr
			(i32.const 0)				;; input_len
			(i32.const 0xffffffff) 		;; u32 max sentinel value: do not copy output
			(i32.const 0)				;; output_len_ptr
		)
		drop

		(call $seal_call_chain_extension
			(i32.load (i32.const 8))	;; _id
			(i32.const 0)				;; input_ptr
			(i32.const 0)				;; input_len
			(i32.const 0xffffffff) 		;; u32 max sentinel value: do not copy output
			(i32.const 0)				;; output_len_ptr
		)
		drop

		(if (i32.eqz (i32.load8_u (i32.const 12)))
			(then
				;; stop recursion
				(i32.store8 (i32.const 12) (i32.const 1))

				;; load own address into buffer
				(call $seal_address (i32.const 16) (i32.const 48))

				;; call function 2 + 3 of chainext 3 next time
				;; (3 << 16) | 2
				;; (3 << 16) | 3
				(i32.store (i32.const 4) (i32.const 196610))
				(i32.store (i32.const 8) (i32.const 196611))

				;; call self
				(call $seal_call
					(i32.const 8) ;; Set ALLOW_REENTRY
					(i32.const 16)  ;; Pointer to "callee" address.
					(i64.const 0)  ;; How much gas to devote for the execution. 0 = all.
					(i32.const 512) ;; Pointer to the buffer with value to transfer
					(i32.const 4) ;; Pointer to input data buffer address
					(i32.load (i32.const 0))  ;; Length of input data buffer
					(i32.const 4294967295) ;; u32 max value is the sentinel value: do not copy output
					(i32.const 0) ;; Length is ignored in this case
				)

				;; check that call succeeded of call
				(call $assert (i32.eqz))
			)
			(else)
		)
	)
)
