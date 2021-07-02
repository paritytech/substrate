(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

    (func (export "deploy")
        (call $ok_trap_revert)
    )

    (func (export "call")
        (call $ok_trap_revert)
    )

    (func $ok_trap_revert
        (i32.store (i32.const 4) (i32.const 4))
        (call $seal_input (i32.const 0) (i32.const 4))
        (block $IF_2
            (block $IF_1
                (block $IF_0
                    (br_table $IF_0 $IF_1 $IF_2
                        (i32.load8_u (i32.const 0))
                    )
                    (unreachable)
                )
                ;; 0 = return with success
                return
            )
            ;; 1 = revert
            (call $seal_return (i32.const 1) (i32.const 0) (i32.const 0))
            (unreachable)
        )
        ;; 2 = trap
        (unreachable)
    )
)
