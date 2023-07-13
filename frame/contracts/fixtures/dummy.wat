;; A valid contract which does nothing at all
(module
	(import "env" "memory" (memory 1 1))
	(func (export "deploy"))
	(func (export "call"))
)
