;; This expects [account_id, gas_limit] as input and calls the account_id with the supplied gas_limit.
;; It returns the result of the call as output data.
(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_call" (func $seal_call (param i32 i32 i64 i32 i32 i32 i32 i32 i32) (result i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; 0x1000 = 4k in little endian
	;; size of input buffer
	(data (i32.const 0) "\00\10")

	(func (export "deploy"))

	(func (export "call")
		;; Receive the encoded call + gas_limit
		(call $seal_input
			(i32.const 4)	;; Pointer to the input buffer
			(i32.const 0)	;; Size of the length buffer
		)
		(i32.store
			(i32.const 0)
			(call $seal_call
				(i32.const 4) ;; Pointer to "callee" address.
				(i32.const 32) ;; Length of "callee" address.
				(i64.load (i32.const 36)) ;; How much gas to devote for the execution.
				(i32.const 0) ;; Pointer to the buffer with value to transfer
				(i32.const 0) ;; Length of the buffer with value to transfer.
				(i32.const 0) ;; Pointer to input data buffer address
				(i32.const 0) ;; Length of input data buffer
				(i32.const 0xffffffff) ;; u32 max sentinel value: do not copy output
				(i32.const 0) ;; Ptr to output buffer len
			)
		)
		(call $seal_return (i32.const 0) (i32.const 0) (i32.const 4))
	)
)
