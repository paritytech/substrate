const PROTOS: &[&str] = &["bitswap.v1.2.0.proto"];

fn main() {
	prost_build::compile_protos(PROTOS, &["src/schema"]).unwrap();
}
