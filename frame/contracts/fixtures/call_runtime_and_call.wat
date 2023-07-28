(module
	(import "seal0" "call_runtime" (func $call_runtime (param i32 i32) (result i32)))
	(import "seal1" "seal_call" (func $seal_call (param i32 i32 i64 i32 i32 i32 i32 i32) (result i32)))
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok (get_local 0))
			(unreachable)
		)
	)

	(func (export "call")
	    ;; Store available input size at offset 0.
        (i32.store (i32.const 0) (i32.const 512))

		;; read input data
        (call $seal_input (i32.const 4) (i32.const 0))

		;; Input data layout.
		;; [0..4) - size of the call
		;; [4..8) - how many bytes to add to storage
		;; [8..40) - address of the callee
		;; [40..n) - encoded runtime call

		;; Invoke call_runtime with the encoded call passed to this contract.
		(call $assert (i32.eqz
			(call $call_runtime
				(i32.const 40)                ;; Pointer where the call is stored
				(i32.sub
					(i32.load (i32.const 0))  ;; Size of the call
					(i32.const 36)            ;; Subtract size of the subcall-related part: 4 bytes for storage length to add + 32 bytes of the callee address 
				)
			)
		))

		;; call passed contract
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

	(func (export "deploy"))
)

