(module
	(import "env" "ext_transfer" (func $ext_transfer (param i32 i32 i32 i32) (result i32)))
	(import "env" "ext_set_storage" (func $ext_set_storage (param i32 i32 i32)))
	(import "env" "ext_clear_storage" (func $ext_clear_storage (param i32)))
	(import "env" "ext_set_rent_allowance" (func $ext_set_rent_allowance (param i32 i32)))
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_read" (func $ext_scratch_read (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; insert a value of 4 bytes into storage
	(func $call_0
		(call $ext_set_storage
			(i32.const 1)
			(i32.const 0)
			(i32.const 4)
		)
	)

	;; remove the value inserted by call_1
	(func $call_1
		(call $ext_clear_storage
			(i32.const 1)
		)
	)

	;; transfer 50 to CHARLIE
	(func $call_2
		(call $assert
			(i32.eq
				(call $ext_transfer (i32.const 68) (i32.const 8) (i32.const 76) (i32.const 8))
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
		(set_local $input_size
			(call $ext_scratch_size)
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
		(local $input_size i32)
		(set_local $input_size
			(call $ext_scratch_size)
		)
		(call $ext_set_storage
			(i32.const 0)
			(i32.const 0)
			(i32.const 4)
		)
		(call $ext_scratch_read
			(i32.const 0)
			(i32.const 0)
			(get_local $input_size)
		)
		(call $ext_set_rent_allowance
			(i32.const 0)
			(get_local $input_size)
		)
	)

	;; Encoding of 10 in balance
	(data (i32.const 0) "\28")

	;; encoding of Charlies's account id
	(data (i32.const 68) "\03")

	;; encoding of 50 balance
	(data (i32.const 76) "\32")
)
