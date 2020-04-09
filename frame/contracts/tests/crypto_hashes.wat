(module
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_read" (func $ext_scratch_read (param i32 i32 i32)))
	(import "env" "ext_scratch_write" (func $ext_scratch_write (param i32 i32)))

	(import "env" "ext_hash_sha2_256" (func $ext_hash_sha2_256 (param i32 i32 i32)))
	(import "env" "ext_hash_keccak_256" (func $ext_hash_keccak_256 (param i32 i32 i32)))
	(import "env" "ext_hash_blake2_256" (func $ext_hash_blake2_256 (param i32 i32 i32)))
	(import "env" "ext_hash_blake2_128" (func $ext_hash_blake2_128 (param i32 i32 i32)))

	(import "env" "memory" (memory 1 1))

	(type $hash_fn_sig (func (param i32 i32 i32)))
	(table 8 funcref)
	(elem (i32.const 1)
		$ext_hash_sha2_256
		$ext_hash_keccak_256
		$ext_hash_blake2_256
		$ext_hash_blake2_128
	)
	(data (i32.const 1) "20202010201008") ;; Output sizes of the hashes in order in hex.

	;; Not in use by the tests besides instantiating the contract.
	(func (export "deploy"))

	;; Called by the tests.
	;;
	;; The `call` function expects data in a certain format in the scratch
	;; buffer.
	;;
	;; 1. The first byte encodes an identifier for the crypto hash function
	;;    under test. (*)
	;; 2. The rest encodes the input data that is directly fed into the
	;;    crypto hash function chosen in 1.
	;;
	;; The `deploy` function then computes the chosen crypto hash function
	;; given the input and puts the result back into the scratch buffer.
	;; After contract execution the test driver then asserts that the returned
	;; values are equal to the expected bytes for the input and chosen hash
	;; function.
	;;
	;; (*) The possible value for the crypto hash identifiers can be found below:
	;;
	;; | value | Algorithm | Bit Width |
	;; |-------|-----------|-----------|
	;; |     0 |      SHA2 |       256 |
	;; |     1 |    KECCAK |       256 |
	;; |     2 |    BLAKE2 |       256 |
	;; |     3 |    BLAKE2 |       128 |
	;; ---------------------------------
	(func (export "call") (result i32)
		(local $chosen_hash_fn i32)
		(local $input_ptr i32)
		(local $input_len i32)
		(local $output_ptr i32)
		(local $output_len i32)
		(local.set $input_ptr (i32.const 10))
		(call $ext_scratch_read (local.get $input_ptr) (i32.const 0) (call $ext_scratch_size))
		(local.set $chosen_hash_fn (i32.load8_u (local.get $input_ptr)))
		(if (i32.gt_u (local.get $chosen_hash_fn) (i32.const 7))
			;; We check that the chosen hash fn  identifier is within bounds: [0,7]
			(unreachable)
		)
		(local.set $input_ptr (i32.add (local.get $input_ptr) (i32.const 1)))
		(local.set $input_len (i32.sub (call $ext_scratch_size) (i32.const 1)))
		(local.set $output_ptr (i32.const 100))
		(local.set $output_len (i32.load8_u (local.get $chosen_hash_fn)))
		(call_indirect (type $hash_fn_sig)
			(local.get $input_ptr)
			(local.get $input_len)
			(local.get $output_ptr)
			(local.get $chosen_hash_fn) ;; Which crypto hash function to execute.
		)
		(call $ext_scratch_write
			(local.get $output_ptr) ;; Linear memory location of the output buffer.
			(local.get $output_len) ;; Number of output buffer bytes.
		)
		(i32.const 0)
	)
)
