;; This contract:
;; 1) Reads signature, message and public key from the input
;; 2) Calls and return the result of sr25519_verify

(module
    ;; import the host functions from the seal0 module
	(import "seal0" "sr25519_verify" (func $sr25519_verify (param i32 i32 i32 i32) (result i32)))
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))

	;; give the program 1 page of memory
	(import "env" "memory" (memory 1 1))

	;; [0, 4) length of signature + message + public key - 64 + 11 + 32 = 107 bytes
	;; write the length of the input (6b = 107) bytes at offset 0
	(data (i32.const 0) "\6b")

	(func (export "deploy"))

	(func (export "call")
		;; define local variables
		(local $signature_ptr i32)
		(local $pub_key_ptr i32)
		(local $message_len i32)
		(local $message_ptr i32)

		;; set the pointers to the memory locations
		;; Memory layout during `call`
		;; [10, 74) signature
		;; [74, 106) public key
		;; [106, 117) message (11 bytes)
		(local.set $signature_ptr (i32.const 10))
		(local.set $pub_key_ptr (i32.const 74))
		(local.set $message_ptr (i32.const 106))

		;; store the input into the memory, starting at the signature and 
		;; up to 107 bytes stored at offset 0
		(call $seal_input (local.get $signature_ptr) (i32.const 0))

		;; call sr25519_verify and store the return code
		(i32.store
			(i32.const 0)
			(call $sr25519_verify
				(local.get $signature_ptr)
				(local.get $pub_key_ptr)
				(i32.const 11)
				(local.get $message_ptr)
			)
		)

		;; exit with success and take transfer return code to the output buffer
		(call $seal_return (i32.const 0) (i32.const 0) (i32.const 4))
	)
)

