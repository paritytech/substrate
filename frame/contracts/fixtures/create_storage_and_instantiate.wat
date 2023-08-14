;; This instantiates another contract and passes some input to its constructor.
(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_set_storage" (func $seal_set_storage (param i32 i32 i32)))
	(import "seal2" "instantiate" (func $seal_instantiate
		(param i32 i64 i64 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32) (result i32)
	))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 8) send 10_000 balance
	(data (i32.const 48) "\10\27\00\00\00\00\00\00")

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
    	;; store length of contract address
        (i32.store (i32.const 84) (i32.const 32))

        ;; copy input at address 4
        (call $seal_input (i32.const 4) (i32.const 0))

		;; memory layout is:
		;; 	[0,4): size of input buffer
		;; 	[4,8): size of the storage to be created in callee
		;; 	[8,40): the code hash of the contract to instantiate
		;; 	[40,48): for the encoded deposit limit
		;; 	[48,52): value to transfer
		;; 	[52,84): address of the deployed contract
		;; 	[84,88): len of the address

		;; instantiate a contract
		(call $assert (i32.eqz
;;		(i32.store
;;		 (i32.const 64)
		 (call $seal_instantiate
				(i32.const 8)	;; Pointer to the code hash.
				(i64.const 0)	;; How much ref_time weight to devote for the execution. 0 = all.
				(i64.const 0)	;; How much proof_size weight to devote for the execution. 0 = all.
				(i32.const 40)	;; Pointer to the storage deposit limit
				(i32.const 48)	;; Pointer to the buffer with value to transfer
				(i32.const 4)	;; Pointer to input data buffer address
				(i32.const 4)	;; Length of input data buffer
				(i32.const 52) 	;; Pointer to where to copy address
				(i32.const 84)	;; Pointer to address len ptr
				(i32.const 0xffffffff) ;; u32 max sentinel value: do not copy output
				(i32.const 0)	;; Length is ignored in this case
				(i32.const 0)	;; salt_ptr
				(i32.const 0)	;; salt_len
			)
		))
		;; return the deployed contract address
		(call $seal_return (i32.const 0) (i32.const 52) (i32.const 32))
	)
)
