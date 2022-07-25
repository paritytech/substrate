(module
	(import "seal0" "seal_set_storage" (func $seal_set_storage (param i32 i32 i32)))
	(import "seal0" "seal_caller" (func $seal_caller (param i32 i32)))
	(import "seal0" "seal_value_transferred" (func $seal_value_transferred (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 32) storage key
	(data (i32.const 0) "\01")

	;; [32, 64) buffer for transferred value

	;; [64, 96) size of the buffer for transferred value
	(data (i32.const 64) "\20")

	;; [96, 128) buffer for the caller

	;; [128, 160) size of the buffer for caller
	(data (i32.const 128) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; place a value in storage
		(call $seal_set_storage
			(i32.const 0)		;; Pointer to storage key
			(i32.const 0)		;; Pointer to value
			(i32.const 32)		;; Size of value
		)

		;; This stores the value transferred in the buffer
		(call $seal_value_transferred (i32.const 32) (i32.const 64))

		;; assert len == 8
		(call $assert
			(i32.eq
				(i32.load (i32.const 64))
				(i32.const 8)
			)
		)

		;; assert that contents of the buffer is equal to the value
		;; passed to the `caller` contract: 1337
		(call $assert
			(i64.eq
				(i64.load (i32.const 32))
				(i64.const 1337)
			)
		)

		;; fill the buffer with the caller.
		(call $seal_caller (i32.const 96) (i32.const 128))

		;; assert len == 32
		(call $assert
			(i32.eq
				(i32.load (i32.const 128))
				(i32.const 32)
			)
		)

		;; assert that the first 64 byte are the beginning of "ALICE",
		;; who is the caller of the `caller` contract
		(call $assert
			(i64.eq
				(i64.load (i32.const 96))
				(i64.const 0x0101010101010101)
			)
		)
	)

	(func (export "deploy"))
)
