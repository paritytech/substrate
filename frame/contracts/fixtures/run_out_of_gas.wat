(module
	(func (export "call")
		(loop $inf (br $inf)) ;; just run out of gas
		(unreachable)
	)
	(func (export "deploy"))
)
