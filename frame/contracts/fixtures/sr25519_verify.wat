;; This contract:
;; 1) Reads signature, message and public key from the input
;; 2) Calls sr25519_verify
;; 3) Traps if the signature is invalid

(module
    ;; import the host functions from the seal0 module
	(import "seal0" "seal_sr25519_verify" (func $seal_sr25519_verify (param i32 i32 i32 i32) (result i32)))
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))

	;; give the program 1 page of memory
	(import "env" "memory" (memory 1 1))

	;; [4, 8) len of signature + message + public key - 64 + 12 + 32 = 108 bytes
	;; write the length of the input (108 bytes) at offset 4
	(data (i32.const 4) "\6c")

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
		;; define local variables
		(local $signature_ptr i32)
		(local $message_ptr i32)
		(local $pub_key_ptr i32)
		(local $result i32)

		;; set the pointers to the memory locations
		;; Memory layout during `call`
		;; [10, 74) signature
		;; [74, 86) message
		;; [86, 118) public key
		(local.set $signature_ptr (i32.const 10))
		(local.set $message_ptr (i32.const 74))
		(local.set $pub_key_ptr (i32.const 86))

		;; store the input into the memory, starting at the signature and 
		;; up to 108 bytes stored at offset 4
		(call $seal_input (local.get $signature_ptr) (i32.const 4))

		;; call sr25519_verify and set the result
		(local.set
			$result
			(call $seal_sr25519_verify
				(local.get $signature_ptr)
				(local.get $message_ptr)
				(i32.const 12)
				(local.get $pub_key_ptr)
			)
		)

		;; trap if the result is not 0x0 (ReturnCode::Success)
		(call $assert
			(i32.eq
				(local.get $result) ;; The result
				(i32.const 0x0) ;; 0x0 - Success result
			)
		)
	)
)

