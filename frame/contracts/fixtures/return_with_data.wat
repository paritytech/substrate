(module
	(import "env" "ext_input" (func $ext_input (param i32 i32)))
	(import "env" "ext_return" (func $ext_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 128) buffer where input is copied

	;; [128, 132) length of the input buffer
	(data (i32.const 128) "\80")

	;; Deploy routine is the same as call.
	(func (export "deploy")
		(call $call)
	)

	;; Call reads the first 4 bytes (LE) as the exit status and returns the rest as output data.
	(func $call (export "call")
		;; Copy input into this contracts memory.
		(call $ext_input (i32.const 0) (i32.const 128))

		;; Copy all but the first 4 bytes of the input data as the output data.
		;; Use the first byte as exit status
		(call $ext_return
			(i32.load8_u (i32.const 0))	;; Exit status
			(i32.const 4)	;; Pointer to the data to return.
			(i32.sub		;; Count of bytes to copy.
				(i32.load (i32.const 128))
				(i32.const 4)
			)
		)
		(unreachable)
	)
)
