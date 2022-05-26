(module
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 32) return value
	(data (i32.const 0) "\02")

	(func (export "deploy"))

	(func (export "call")
		(call $seal_return (i32.const 0) (i32.const 0) (i32.const 4))
	)
)
