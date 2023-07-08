;; Valid module but missing the call function
(module
	(import "env" "memory" (memory 1 1))
	(func (export "deploy"))
)
