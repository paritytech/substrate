const PROTOS: &[&str] = &["src/schema/light.v1.proto"];

fn main() {
	prost_build::compile_protos(PROTOS, &["src/schema"]).unwrap();
}
