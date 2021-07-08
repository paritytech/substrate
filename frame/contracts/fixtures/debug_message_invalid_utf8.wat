;; Emit a "Hello World!" debug message
(module
	(import "__unstable__" "seal_debug_message" (func $seal_debug_message (param i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))

	(data (i32.const 0) "\fc")

	(func (export "call")
		(call $seal_debug_message
			(i32.const 0)	;; Pointer to the text buffer
			(i32.const 12)	;; The size of the buffer
		)
		;; the above call traps because we supplied invalid utf8
		unreachable
	)

	(func (export "deploy"))
)
