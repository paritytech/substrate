use crate::{Fq, Fr};
use ark_algebra_test_templates::*;
use ark_ff::{
	biginteger::BigInteger256 as BigInteger,
	fields::{Field, LegendreSymbol::*},
	One, Zero,
};
use ark_std::str::FromStr;

test_field!(fr; Fr; mont_prime_field);
test_field!(fq; Fq; mont_prime_field);

#[test]
fn test_fq_add() {
	let f1 = Fq::from_str(
		"18386742314266644595564329008376577163854043021652781768352795308532764650733",
	)
	.unwrap();
	let f2 = Fq::from_str(
		"39786307610986038981023499868190793548353538256264351797285876981647142458383",
	)
	.unwrap();
	let f3 = Fq::from_str(
		"5737174750126493097140088368381404874517028777389495743035013590241325924603",
	)
	.unwrap();
	assert!(!f1.is_zero());
	assert!(!f2.is_zero());
	assert!(!f3.is_zero());
	assert_eq!(f1 + &f2, f3);
}

#[test]
fn test_fq_add_one() {
	let f1 = Fq::from_str(
		"4946875394261337176810256604189376311946643975348516311606738923340201185904",
	)
	.unwrap();
	let f2 = Fq::from_str(
		"4946875394261337176810256604189376311946643975348516311606738923340201185905",
	)
	.unwrap();
	assert!(!f1.is_zero());
	assert!(!f2.is_zero());
	assert_eq!(f1 + &Fq::one(), f2);
}

#[test]
fn test_fq_mul() {
	let f1 = Fq::from_str(
		"24703123148064348394273033316595937198355721297494556079070134653139656190956",
	)
	.unwrap();
	let f2 = Fq::from_str(
		"38196797080882758914424853878212529985425118523754343117256179679117054302131",
	)
	.unwrap();
	let f3 = Fq::from_str(
		"38057113854472161555556064369220825628027487067886761874351491955834635348140",
	)
	.unwrap();
	assert!(!f1.is_zero());
	assert!(!f2.is_zero());
	assert!(!f3.is_zero());
	assert_eq!(f1 * &f2, f3);
}

#[test]
fn test_fq_triple_mul() {
	let f1 = Fq::from_str(
		"23834398828139479510988224171342199299644042568628082836691700490363123893905",
	)
	.unwrap();
	let f2 = Fq::from_str(
		"48343809612844640454129919255697536258606705076971130519928764925719046689317",
	)
	.unwrap();
	let f3 = Fq::from_str(
		"22704845471524346880579660022678666462201713488283356385810726260959369106033",
	)
	.unwrap();
	let f4 = Fq::from_str(
		"18897508522635316277030308074760673440128491438505204942623624791502972539393",
	)
	.unwrap();
	assert!(!f1.is_zero());
	assert!(!f2.is_zero());
	assert!(!f3.is_zero());
	assert_eq!(f1 * &f2 * &f3, f4);
}

#[test]
fn test_fq_div() {
	let f1 = Fq::from_str(
		"31892744363926593013886463524057935370302352424137349660481695792871889573091",
	)
	.unwrap();
	let f2 = Fq::from_str(
		"47695868328933459965610498875668250916462767196500056002116961816137113470902",
	)
	.unwrap();
	let f3 = Fq::from_str(
		"29049672724678710659792141917402891276693777283079976086581207190825261000580",
	)
	.unwrap();
	assert!(!f1.is_zero());
	assert!(!f2.is_zero());
	assert!(!f3.is_zero());
	assert_eq!(f1 / &f2, f3);
}

#[test]
fn test_fq_sub() {
	let f1 = Fq::from_str(
		"18695869713129401390241150743745601908470616448391638969502807001833388904079",
	)
	.unwrap();
	let f2 = Fq::from_str(
		"10105476028534616828778879109836101003805485072436929139123765141153277007373",
	)
	.unwrap();
	let f3 = Fq::from_str(
		"8590393684594784561462271633909500904665131375954709830379041860680111896706",
	)
	.unwrap();
	assert!(!f1.is_zero());
	assert!(!f2.is_zero());
	assert!(!f3.is_zero());
	assert_eq!(f1 - &f2, f3);
}

#[test]
fn test_fq_double_in_place_thrice() {
	let mut f1 = Fq::from_str(
		"32768907806651393940832831055386272949401004221411141755415956893066040832473",
	)
	.unwrap();
	let f3 = Fq::from_str(
		"52407761752706389608871686410346320244445823769178582752913020344774001921732",
	)
	.unwrap();
	assert!(!f1.is_zero());
	assert!(!f3.is_zero());
	f1.double_in_place();
	f1.double_in_place();
	f1.double_in_place();
	assert_eq!(f1, f3);
}

#[test]
fn test_fq_generate_random_ed_on_bls12_381_point() {
	let d = Fq::from_str(
		"19257038036680949359750312669786877991949435402254120286184196891950884077233",
	)
	.unwrap();
	let y = Fq::from_str(
		"20269054604167148422407276086932743904275456233139568486008667107872965128512",
	)
	.unwrap();
	let x2 = Fq::from_str(
		"35041048504708632193693740149219726446678304552734087046982753200179718192840",
	)
	.unwrap();

	let computed_y2 = y.square();
	let y2 = Fq::from_str(
		"22730681238307918419349440108285755984465605552827817317611903495170775437833",
	)
	.unwrap();
	assert_eq!(y2, computed_y2);

	let computed_dy2 = d * &computed_y2;
	let dy2 = Fq::from_str(
		"24720347560552809545835752815204882739669031262711919770503096707526812943411",
	)
	.unwrap();
	assert_eq!(dy2, computed_dy2);

	let computed_divisor = computed_dy2 + &Fq::one();
	let divisor = Fq::from_str(
		"24720347560552809545835752815204882739669031262711919770503096707526812943412",
	)
	.unwrap();
	assert_eq!(divisor, computed_divisor);

	let computed_x2 = (computed_y2 - &Fq::one()) / &computed_divisor;
	assert_eq!(x2, computed_x2);

	let x = Fq::from_str(
		"15337652609730546173818014678723269532482775720866471265774032070871608223361",
	)
	.unwrap();
	let computed_x = computed_x2.sqrt().unwrap();
	assert_eq!(computed_x.square(), x2);
	assert_eq!(x, computed_x);

	fn add<'a>(curr: (Fq, Fq), other: &'a (Fq, Fq)) -> (Fq, Fq) {
		let y1y2 = curr.1 * &other.1;
		let x1x2 = curr.0 * &other.0;
		let d = Fq::from_str(
			"19257038036680949359750312669786877991949435402254120286184196891950884077233",
		)
		.unwrap();
		let dx1x2y1y2 = d * &y1y2 * &x1x2;

		let d1 = Fq::one() + &dx1x2y1y2;
		let d2 = Fq::one() - &dx1x2y1y2;

		let x1y2 = curr.0 * &other.1;
		let y1x2 = curr.1 * &other.0;

		let x = (x1y2 + &y1x2) / &d1;
		let y = (y1y2 + &x1x2) / &d2;

		(x, y)
	}

	let result = add((x, y), &(x, y));
	let result = add(result, &result);
	let result = add(result, &result);

	let point_x = Fq::from_str(
		"47259664076168047050113154262636619161204477920503059672059915868534495873964",
	)
	.unwrap();
	let point_y = Fq::from_str(
		"19016409245280491801573912449420132838852726543024859389273314249842195919690",
	)
	.unwrap();
	assert_eq!((point_x, point_y), result);
}

#[test]
fn test_fq_square_in_place() {
	let mut f1 = Fq::from_str(
		"34864651240005695523200639428464570946052769938774601449735727714436878540682",
	)
	.unwrap();
	let f3 =
		Fq::from_str("213133100629336594719108316042277780359104840987226496279264105585804377948")
			.unwrap();
	assert!(!f1.is_zero());
	assert!(!f3.is_zero());
	f1.square_in_place();
	assert_eq!(f1, f3);
}

#[test]
fn test_fq_from_str() {
	let f1_from_repr = Fq::from(BigInteger::new([
		0xab8a2535947d1a77,
		0x9ba74cbfda0bbcda,
		0xe928b59724d60baf,
		0x1cccaaeb9bb1680a,
	]));
	let f1 = Fq::from_str(
		"13026376210409056429264774981357153555336288129100724591327877625017068755575",
	)
	.unwrap();
	let f2_from_repr = Fq::from(BigInteger::new([
		0x97e9103775d2f35c,
		0xbe6756b6c587544b,
		0x6ee38c3afd88ef4b,
		0x2bacd150f540c677,
	]));
	let f2 = Fq::from_str(
		"19754794831832707859764530223239420866832328728734160755396495950822165902172",
	)
	.unwrap();
	assert_eq!(f1_from_repr, f1);
	assert_eq!(f2_from_repr, f2);
}

#[test]
fn test_fq_legendre() {
	assert_eq!(QuadraticResidue, Fq::one().legendre());
	assert_eq!(Zero, Fq::zero().legendre());

	let e = BigInteger::new([
		0x0dbc5349cd5664da,
		0x8ac5b6296e3ae29d,
		0x127cb819feceaa3b,
		0x3a6b21fb03867191,
	]);
	assert_eq!(QuadraticResidue, Fq::from(e).legendre());
	let e = BigInteger::new([
		0x96341aefd047c045,
		0x9b5f4254500a4d65,
		0x1ee08223b68ac240,
		0x31d9cd545c0ec7c6,
	]);
	assert_eq!(QuadraticNonResidue, Fq::from(e).legendre());
}

#[test]
fn test_fr_add() {
	let f1 = Fr::from(BigInteger::new([
		0xc81265fb4130fe0c,
		0xb308836c14e22279,
		0x699e887f96bff372,
		0x84ecc7e76c11ad,
	]));
	let f2 = Fr::from(BigInteger::new([
		0x71875719b422efb8,
		0x43658e68a93612,
		0x9fa756be2011e833,
		0xaa2b2cb08dac497,
	]));
	let f3 = Fr::from(BigInteger::new([
		0x3999bd14f553edc4,
		0xb34be8fa7d8b588c,
		0x945df3db6d1dba5,
		0xb279f92f046d645,
	]));
	assert_eq!(f1 + &f2, f3);
}

#[test]
fn test_fr_mul() {
	let f1 = Fr::from(BigInteger::new([
		0xc81265fb4130fe0c,
		0xb308836c14e22279,
		0x699e887f96bff372,
		0x84ecc7e76c11ad,
	]));
	let f2 = Fr::from(BigInteger::new([
		0x71875719b422efb8,
		0x43658e68a93612,
		0x9fa756be2011e833,
		0xaa2b2cb08dac497,
	]));
	let f3 = Fr::from(BigInteger::new([
		0x6d6618ac6b4a8381,
		0x5b9eb35d711ee1da,
		0xce83310e6ac4105d,
		0x98032e0f206320a,
	]));
	assert_eq!(f1 * &f2, f3);
}

#[test]
fn test_fr_from_str() {
	let f100_from_repr = Fr::from(BigInteger::new([0x64, 0, 0, 0]));
	let f100 = Fr::from_str("100").unwrap();
	assert_eq!(f100_from_repr, f100);
}
