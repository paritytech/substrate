default:
	#export CPATH=.:/home/michi/projects/wabt/wasm2c/:$CPATH

	./scripts/build.sh && \
	wasm2c node/runtime/wasm/target/wasm32-unknown-unknown/release/node_runtime.compact.wasm -o node_runtime.c && \
	./transform.sh && \
	gcc -fPIC -rdynamic -shared -o libnode_runtime.so node_runtime.c wasm-rt-impl.c && \
	cp -f libnode_runtime.so target/release/deps/

display_exports:
	readelf -Ws libruntime_test.so
