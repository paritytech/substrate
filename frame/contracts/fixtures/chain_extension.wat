;; Call chain extension by passing through input and output of this contract
(module
	(import "seal0" "seal_call_chain_extension"
		(func $seal_call_chain_extension (param i32 i32 i32 i32 i32) (result i32))
	)
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 16 16))

	(func $assert (param i32)
		(block $ok
			(br_if $ok (get_local 0))
			(unreachable)
		)
	)

	;; [0, 4) len of input output
	(data (i32.const 0) "\02")

	;; [4, 12) buffer for input

	;; [12, 16) len of output buffer
	(data (i32.const 12) "\02")

	;; [16, inf) buffer for output

	(func (export "deploy"))

	(func (export "call")
		(call $seal_input (i32.const 4) (i32.const 0))

		;; the chain extension passes through the input and returns it as output
		(call $seal_call_chain_extension
			(i32.load8_u (i32.const 4))	;; func_id
			(i32.const 4)				;; input_ptr
			(i32.load (i32.const 0))	;; input_len
			(i32.const 16)				;; output_ptr
			(i32.const 12)				;; output_len_ptr
		)

		;; the chain extension passes through the func_id
		(call $assert (i32.eq (i32.load8_u (i32.const 4))))

		(call $seal_return (i32.const 0) (i32.const 16) (i32.load (i32.const 12)))
	)
)
