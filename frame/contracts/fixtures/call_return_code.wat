;; This calls the supplied dest and transfers 100 balance during this call and copies
;; the return code of this call to the output buffer.
;; It also forwards its input to the callee.
(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_call" (func $seal_call (param i32 i32 i64 i32 i32 i32 i32 i32 i32) (result i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 8) 100 balance
	(data (i32.const 0) "\64\00\00\00\00\00\00\00")

	;; [8, 12) here we store the return code of the transfer

	;; [12, 16) size of the input data
	(data (i32.const 12) "\24")

	;; [16, inf) here we store the input data
	;; 32 byte dest + 4 byte forward

	(func (export "deploy"))

	(func (export "call")
		(call $seal_input (i32.const 16) (i32.const 12))
		(i32.store
			(i32.const 8)
			(call $seal_call
				(i32.const 16) ;; Pointer to "callee" address.
				(i32.const 32) ;; Length of "callee" address.
				(i64.const 0) ;; How much gas to devote for the execution. 0 = all.
				(i32.const 0) ;; Pointer to the buffer with value to transfer
				(i32.const 8) ;; Length of the buffer with value to transfer.
				(i32.const 48) ;; Pointer to input data buffer address
				(i32.const 4) ;; Length of input data buffer
				(i32.const 0xffffffff) ;; u32 max sentinel value: do not copy output
				(i32.const 0) ;; Ptr to output buffer len
			)
		)
		;; exit with success and take transfer return code to the output buffer
		(call $seal_return (i32.const 0) (i32.const 8) (i32.const 4))
	)
)
