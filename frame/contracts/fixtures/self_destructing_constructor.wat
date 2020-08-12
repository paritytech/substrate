(module
	(import "seal0" "seal_terminate" (func $seal_terminate (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "deploy")
		;; Self-destruct by sending full balance to the 0 address.
		(call $seal_terminate
			(i32.const 0)	;; Pointer to destination address
			(i32.const 8)	;; Length of destination address
		)
	)

	(func (export "call"))
)
