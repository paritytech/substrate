;; A valid contract which does nothing at all but imports an invalid function
(module
	(import "invalid" "invalid_88_99" (func (param i32 i32 i32)))
	(func (export "deploy"))
	(func (export "call"))
)
