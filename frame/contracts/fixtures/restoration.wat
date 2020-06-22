(module
	(import "env" "ext_set_storage" (func $ext_set_storage (param i32 i32 i32)))
	(import "env" "ext_restore_to" (func $ext_restore_to (param i32 i32 i32 i32 i32 i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "call")
		(call $ext_restore_to
			;; Pointer and length of the encoded dest buffer.
			(i32.const 256)
			(i32.const 8)
			;; Pointer and length of the encoded code hash buffer
			(i32.const 264)
			(i32.const 32)
			;; Pointer and length of the encoded rent_allowance buffer
			(i32.const 296)
			(i32.const 8)
			;; Pointer and number of items in the delta buffer.
			;; This buffer specifies multiple keys for removal before restoration.
			(i32.const 100)
			(i32.const 1)
		)
	)
	(func (export "deploy")
		;; Data to restore
		(call $ext_set_storage
			(i32.const 0)
			(i32.const 0)
			(i32.const 4)
		)

		;; ACL
		(call $ext_set_storage
			(i32.const 100)
			(i32.const 0)
			(i32.const 4)
		)
	)

	;; Data to restore
	(data (i32.const 0) "\28")

	;; Buffer that has ACL storage keys.
	(data (i32.const 100) "\01")

	;; Address of bob
	(data (i32.const 256) "\02\00\00\00\00\00\00\00")

	;; Code hash of SET_RENT
	(data (i32.const 264)
		"\ab\d6\58\65\1e\83\6e\4a\18\0d\f2\6d\bc\42\ba\e9"
		"\3d\64\76\e5\30\5b\33\46\bb\4d\43\99\38\21\ee\32"
	)

	;; Rent allowance
	(data (i32.const 296) "\32\00\00\00\00\00\00\00")
)
