;; Everything prepared for the host function call, but no call is performed.
(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 8) buffer to write input

	;; [8, 12) size of the input buffer
	(data (i32.const 8) "\04")

	(func (export "call"))

	(func (export "deploy"))
)
