;; This contract:
;; 1) Reads signature, message and public key from the input
;; 2) Calls sr25519_verify
;; 3) Traps if the signature is invalid

(module
	(import "seal0" "seal_sr25519_verify" (func $seal_sr25519_verify (param i32 i32 i32 i32) (result i32)))
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; [4, 8) len of signature + message + public key - 64 + 12 + 32 = 108 bytes
	(data (i32.const 4) "\6c")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	;; Memory layout during `call`
	;; [10, 75) signature
	;; [75, 86) message
	;; [86, 118) public key


	(func (export "deploy"))

	(func (export "call")
		(local $signature_ptr i32)
		(local $message_ptr i32)
		(local $pub_key_ptr i32)
		(local $result i32)

		(local.set $signature_ptr (i32.const 10))
		(local.set $message_ptr (i32.const 74))
		(local.set $pub_key_ptr (i32.const 86))

		;; Read signature, message and public key - 107 bytes
		(call $seal_input (local.get $signature_ptr) (i32.const 4))
		(local.set
			$result
			(call $seal_sr25519_verify
				(local.get $signature_ptr)
				(local.get $message_ptr)
				(i32.const 12)
				(local.get $pub_key_ptr)
			)
		)

		(call $assert
			(i32.eq
				(local.get $result) ;; The result
				(i32.const 0x0) ;; 0x0 - Success result
			)
		)
	)
)

