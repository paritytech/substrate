(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_call" (func $seal_call (param i32 i32 i64 i32 i32 i32 i32 i32 i32) (result i32)))
	(import "seal0" "seal_delegate_call" (func $seal_delegate_call (param i32 i32 i32 i32 i32 i32) (result i32)))
	(import "__unstable__" "seal_reentrant_count" (func $seal_reentrant_count (result i32)))
	(import "env" "memory" (memory 1 1))

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
	    (local $exit_code i32)
		(local $reentrant_count i32)

		(set_local $reentrant_count
			(call $seal_reentrant_count)
		)

		(get_local $reentrant_count)
        (if
            (then
		        ;; assert reentrant_count == 1
		        (call $assert
		        	(i32.eq (get_local $reentrant_count) (i32.const 1))
		        )

                ;; Delegated call to itself
		        (set_local $exit_code
		        	(call $seal_delegate_call
		        		(i32.const 0)	;; Set no call flags (reentrance is forbidden)
		        		(i32.const 0)	;; Pointer to "callee" code_hash.
		        		(i32.const 0)	;; Input is ignored
		        		(i32.const 0)	;; Length of the input
		        		(i32.const 0xffffffff)	;; u32 max sentinel value: do not copy output
		        		(i32.const 0)	;; Length is ignored in this case
		        	)
		        )

		        ;; Second reentrance is forbidden
		        (call $assert
		        	(i32.eq (get_local $exit_code) (i32.const 1))
		        )
            )
            (else
		        ;; Reading "callee" contract address (which is the address of the caller)
		        (call $seal_input (i32.const 0) (i32.const 32))

                ;; Call to itself
		        (set_local $exit_code
		        	(call $seal_call
		        		(i32.const 0)	;; Pointer to "callee" address.
		        		(i32.const 32)	;; Length of "callee" address.
		        		(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
		        		(i32.const 0)	;; Pointer to the buffer with value to transfer
		        		(i32.const 0)	;; Length of the buffer with value to transfer.
		        		(i32.const 0)	;; Pointer to input data buffer address
		        		(i32.const 32)	;; Length of input data buffer
		                (i32.const 0xffffffff) ;; u32 max sentinel value: do not copy output
		                (i32.const 0) ;; Ptr to output buffer len
		        	)
		        )

		        ;; Check for status code 1, due to reentrance in delegated call.
		        (call $assert
		        	(i32.eq (get_local $exit_code) (i32.const 1)) ;; ReturnCode::ContractTrapped
		        )
            )
        )
	)

	(func (export "deploy"))

)
