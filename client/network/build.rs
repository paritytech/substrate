const PROTOS: &[&str] = &[
	"src/schema/api.v1.proto",
	"src/schema/light.v1.proto"
];

fn main() {
	prost_build::compile_protos(PROTOS, &["src/schema"]).unwrap();
}
