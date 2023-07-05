fn main() {
	prost_build::compile_protos(
		&["src/worker/schema/dht-v1.proto", "src/worker/schema/dht-v2.proto"],
		&["src/worker/schema"],
	)
	.unwrap();
}
