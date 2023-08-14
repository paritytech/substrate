;; Stores a value of the passed size. The host function is called once.
(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 8) buffer to write input

	;; [8, 12) size of the input buffer
	(data (i32.const 8) "\04")

	(func (export "call")
		;; instructions to consume engine fuel
		(drop
			(i32.const 42)
		 )

 	    (call $seal_input (i32.const 0) (i32.const 8))

	 )

	(func (export "deploy"))
)
