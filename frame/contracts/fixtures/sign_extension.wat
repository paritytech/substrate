(module
	(import "env" "memory" (memory 1 1))
	(func (export "deploy"))
	(func (export "call"))
	(func (param i32) (result i32)
		local.get 0
		i32.extend8_s
	)
)
