;; An invalid module
(module
	(func (export "deploy"))
	(func (export "call")
		;; imbalanced stack
		(i32.const 7)
	)
)
