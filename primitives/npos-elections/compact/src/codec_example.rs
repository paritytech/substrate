//! A simpler example of how compact encoding works. Not to be merged, just for review assistance.
//! Run with `cargo play codec_example.rs`

//# parity-scale-codec = { version = "*", features = ["derive"] }

use parity_scale_codec::{Encode, Decode, Compact, Input, Error};

#[derive(Default, Eq, PartialEq, Debug)]
struct BareSolution {
	votes1: Vec<(u32, u16)>,
	votes2: Vec<(u32, (u16, u64), u16)>,
	votes3: Vec<(u32, [(u16, u64); 2usize], u16)>,
}

impl Encode for BareSolution {
	fn encode(&self) -> Vec<u8> {
		let mut r = vec![];

		let votes1 = self.votes1
			.iter()
			.map(|(v, t)| (Compact(*v), Compact(*t)))
			.collect::<Vec<_>>();
		votes1.encode_to(&mut r);

		let votes2 = self.votes2
			.iter()
			.map(|(v, (t1, w), t2)| (
				Compact(*v),
				(
					Compact(*t1),
					Compact(*w),
				),
				Compact(*t2),
			))
			.collect::<Vec<_>>();
		votes2.encode_to(&mut r);

		let votes3 = self.votes3
			.iter()
			.map(|(v, inners, t_last)| {
				let inners_compact_array = [
					(Compact(inners[0].0), Compact(inners[0].1)),
					(Compact(inners[1].0), Compact(inners[1].1)),
				];
				(Compact(*v), inners_compact_array, Compact(*t_last))
			}).collect::<Vec<_>>();

		votes3.encode_to(&mut r);
		r
	}
}

impl Decode for BareSolution {
	fn decode<I: Input>(value: &mut I) -> Result<Self, Error> {
		let votes1 = <Vec<(Compact<u32>, Compact<u16>)> as Decode>::decode(value)?;
		let votes1 = votes1.into_iter().map(|(v, t)| (v.0, t.0)).collect::<Vec<_>>();

		let votes2 = <Vec<(Compact<u32>, (Compact<u16>, Compact<u64>), Compact<u16>)> as Decode>::decode(value)?;
		let votes2 = votes2.into_iter().map(|(v, (t1, w), t2)| (v.0, (t1.0, w.0), t2.into())).collect::<Vec<_>>();

		let votes3 = <Vec<(Compact<u32>, [(Compact<u16>, Compact<u64>); 2], Compact<u16>)> as Decode>::decode(value)?;
		let votes3 = votes3
			.into_iter()
			.map(|(v, inner, t_last)| (
				v.0,
				[
					((inner[0].0).0, (inner[0].1).0),
					((inner[1].0).0, (inner[1].1).0)
				],
				t_last.0,
			))
			.collect::<Vec<_>>();

		Ok(Self {
			votes1,
			votes2,
			votes3,
			..Default::default()
		})
	}
}

fn main() {
	let s = BareSolution {
		votes1: vec![(1,2), (3, 1)],
		votes2: vec![(1, (99, 33), 44), (2, (99, 33), 44)],
		votes3: vec![
			(1, [(99, 33), (55, 33)], 44),
			(2, [(99, 33), (55, 33)], 44),
		]
	};

	let e = s.encode();
	let d = <BareSolution as Decode>::decode(&mut &*e).unwrap();
	assert_eq!(d, s);
}
