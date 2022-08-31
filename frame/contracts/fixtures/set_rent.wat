(module
	(import "seal0" "seal_transfer" (func $seal_transfer (param i32 i32 i32 i32) (result i32)))
	(import "seal0" "seal_set_storage" (func $seal_set_storage (param i32 i32 i32)))
	(import "seal0" "seal_clear_storage" (func $seal_clear_storage (param i32)))
	(import "seal0" "seal_set_rent_allowance" (func $seal_set_rent_allowance (param i32 i32)))
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; insert a value of 4 bytes into storage
	(func $call_0
		(call $seal_set_storage
			(i32.const 1)
			(i32.const 0)
			(i32.const 4)
		)
	)

	;; remove the value inserted by call_1
	(func $call_1
		(call $seal_clear_storage
			(i32.const 1)
		)
	)

	;; transfer 50 to CHARLIE
	(func $call_2
		(call $assert
			(i32.eq
				(call $seal_transfer (i32.const 136) (i32.const 32) (i32.const 100) (i32.const 8))
				(i32.const 0)
			)
		)
	)

	;; do nothing
	(func $call_else)

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	;; Dispatch the call according to input size
	(func (export "call")
		(local $input_size i32)
		;; 4 byte i32 for br_table followed by 32 byte destination for transfer
		(i32.store (i32.const 128) (i32.const 36))
		(call $seal_input (i32.const 132) (i32.const 128))
		(set_local $input_size
			(i32.load (i32.const 132))
		)
		(block $IF_ELSE
			(block $IF_2
				(block $IF_1
					(block $IF_0
						(br_table $IF_0 $IF_1 $IF_2 $IF_ELSE
							(get_local $input_size)
						)
						(unreachable)
					)
					(call $call_0)
					return
				)
				(call $call_1)
				return
			)
			(call $call_2)
			return
		)
		(call $call_else)
	)

	;; Set into storage a 4 bytes value
	;; Set call set_rent_allowance with input
	(func (export "deploy")
		(call $seal_set_storage
			(i32.const 0)
			(i32.const 0)
			(i32.const 4)
		)
		(i32.store (i32.const 128) (i32.const 64))
		(call $seal_input
			(i32.const 132)
			(i32.const 128)
		)
		(call $seal_set_rent_allowance
			(i32.const 132)
			(i32.load (i32.const 128))
		)
	)

	;; Encoding of 10 in balance
	(data (i32.const 0) "\28")

	;; encoding of 50 balance
	(data (i32.const 100) "\32")

	;; [128, 132) size of seal input buffer

	;; [132, inf) output buffer for seal input
)
