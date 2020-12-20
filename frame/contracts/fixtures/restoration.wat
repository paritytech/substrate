(module
	(import "seal0" "seal_set_storage" (func $seal_set_storage (param i32 i32 i32)))
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_restore_to"
		(func $seal_restore_to
			(param i32 i32 i32 i32 i32 i32 i32 i32)
		)
	)
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; copy code hash to contract memory
		(call $seal_input (i32.const 308) (i32.const 304))
		(call $assert
			(i32.eq
				(i32.load (i32.const 304))
				(i32.const 64)
			)
		)
		(call $seal_restore_to
			;; Pointer and length of the encoded dest buffer.
			(i32.const 340)
			(i32.const 32)
			;; Pointer and length of the encoded code hash buffer
			(i32.const 308)
			(i32.const 32)
			;; Pointer and length of the encoded rent_allowance buffer
			(i32.const 296)
			(i32.const 8)
			;; Pointer and number of items in the delta buffer.
			;; This buffer specifies multiple keys for removal before restoration.
			(i32.const 100)
			(i32.const 1)
		)
	)
	(func (export "deploy")
		;; Data to restore
		(call $seal_set_storage
			(i32.const 0)
			(i32.const 0)
			(i32.const 4)
		)

		;; ACL
		(call $seal_set_storage
			(i32.const 100)
			(i32.const 0)
			(i32.const 4)
		)
	)

	;; Data to restore
	(data (i32.const 0) "\28")

	;; Buffer that has ACL storage keys.
	(data (i32.const 100) "\01")

	;; [296, 304) Rent allowance
	(data (i32.const 296) "\32\00\00\00\00\00\00\00")

	;; [304, 308) Size of the buffer that holds code_hash + addr
	(data (i32.const 304) "\40")

	;; [308, 340) code hash of bob (copied by seal_input)
	;; [340, 372) addr of bob (copied by seal_input)
)
