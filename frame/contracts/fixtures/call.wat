;; This calls another contract as passed as its account id.
(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal1" "seal_call" (func $seal_call (param i32 i32 i64 i32 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

    (func (export "deploy"))

    (func (export "call")
    	;; Store length of input buffer.
        (i32.store (i32.const 0) (i32.const 512))

        ;; Copy input at address 4.
        (call $seal_input (i32.const 4) (i32.const 0))

		;; Call passed contract.
		(call $assert (i32.eqz
			(call $seal_call
				(i32.const 0) ;; No flags
				(i32.const 8)  ;; Pointer to "callee" address.
				(i64.const 0)  ;; How much gas to devote for the execution. 0 = all.
				(i32.const 512) ;; Pointer to the buffer with value to transfer
				(i32.const 4) ;; Pointer to input data buffer address
				(i32.const 4)  ;; Length of input data buffer
				(i32.const 4294967295) ;; u32 max value is the sentinel value: do not copy output
				(i32.const 0) ;; Length is ignored in this case
			)
		))
	)
)
