fn main() {
	prost_build::compile_protos(&["src/worker/schema/dht.proto"], &["src/worker/schema"]).unwrap();
}
