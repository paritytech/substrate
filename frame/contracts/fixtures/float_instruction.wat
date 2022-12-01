;; Module that contains a float instruction which is illegal in deterministic mode
(module
	(func (export "call")
		f32.const 1
		drop
	)
	(func (export "deploy")
		f32.const 2
        drop
	)
)
