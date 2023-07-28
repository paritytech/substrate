;; Module that contains a float instruction which is illegal in deterministic mode
(module
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		f32.const 1
		drop
	)
	(func (export "deploy")
		f32.const 2
        drop
	)
)
