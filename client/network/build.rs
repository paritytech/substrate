const PROTOS: &[&str] = &[
	"src/protocol/schema/api.v1.proto",
	"src/protocol/schema/light.v1.proto"
];

fn main() {
	prost_build::compile_protos(PROTOS, &["src/protocol"]).unwrap();
}
