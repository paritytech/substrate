fn main() {
	prost_build::compile_protos(&["src/schema/dht.proto"], &["src/schema"]).unwrap();
}
