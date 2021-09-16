;; This contract:
;; 1) Reads signature and message hash from the input
;; 2) Calls ecdsa_recover
;; 3) Validates that result is Success
;; 4) Returns recovered compressed public key
(module
	(import "__unstable__" "seal_ecdsa_recover" (func $seal_ecdsa_recover (param i32 i32 i32) (result i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
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

	;; [4, 8) len of signature + message hash - 65 bytes + 32 byte = 97 bytes
	(data (i32.const 4) "\61")

	;; Memory layout during `call`
	;; [10, 75) signature
	;; [75, 107) message hash
	(func (export "call")
		(local $signature_ptr i32)
		(local $message_hash_ptr i32)
		(local $result i32)
		(local.set $signature_ptr (i32.const 10))
		(local.set $message_hash_ptr (i32.const 75))
		;; Read signature and message hash - 97 bytes
		(call $seal_input (local.get $signature_ptr) (i32.const 4))
		(local.set
			$result
			(call $seal_ecdsa_recover
				(local.get $signature_ptr)
				(local.get $message_hash_ptr)
				(local.get $signature_ptr) ;; Store output into message signature ptr, because we don't need it anymore
			)
		)
		(call $assert
			(i32.eq
				(local.get $result) ;; The result of recovery execution
				(i32.const 0x0) ;; 0x0 - Success result
			)
		)

		;; exit with success and return recovered public key
		(call $seal_return (i32.const 0) (local.get $signature_ptr) (i32.const 33))
	)
)
