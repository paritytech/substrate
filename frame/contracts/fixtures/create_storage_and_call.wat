;; This calls another contract as passed as its account id. It also creates some storage.
(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_set_storage" (func $seal_set_storage (param i32 i32 i32)))
	(import "seal2" "call" (func $seal_call (param i32 i32 i64 i64 i32 i32 i32 i32 i32 i32) (result i32)))
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
    	;; store length of input buffer
        (i32.store (i32.const 0) (i32.const 512))

        ;; copy input at address 4:
		;; first 4 bytes for the size of the storage to be created in callee
		;; next 32 bytes are for the callee address
		;; next bytes for the encoded deposit limit
        (call $seal_input (i32.const 4) (i32.const 0))

       	;; create 4 byte of storage before calling
		(call $seal_set_storage
			(i32.const 0)		;; Pointer to storage key
			(i32.const 0)		;; Pointer to value
			(i32.const 4)		;; Size of value
		)

		;; call passed contract
		(call $assert (i32.eqz
			(call $seal_call
				(i32.const 0) ;; No flags
				(i32.const 8)  ;; Pointer to "callee" address
				(i64.const 0)  ;; How much ref_time to devote for the execution. 0 = all
				(i64.const 0)  ;; How much proof_limit to devote for the execution. 0 = all
				(i32.const 40) ;; Pointer to the storage deposit limit
				(i32.const 512) ;; Pointer to the buffer with value to transfer
				(i32.const 4) ;; Pointer to input data buffer address
				(i32.const 4)  ;; Length of input data buffer
				(i32.const 4294967295) ;; u32 max value is the sentinel value: do not copy output
				(i32.const 0) ;; Length is ignored in this case
			)
		))

		;; create 8 byte of storage after calling
		;; item of 12 bytes because we override 4 bytes
		(call $seal_set_storage
			(i32.const 0)		;; Pointer to storage key
			(i32.const 0)		;; Pointer to value
			(i32.const 12)		;; Size of value
		)
	)
)
