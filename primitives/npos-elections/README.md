A set of election algorithms to be used with a substrate runtime, typically within the staking
sub-system. Notable implementation include:

- [`seq_phragmen`]: Implements the Phragmén Sequential Method. An un-ranked, relatively fast
  election method that ensures PJR, but does not provide a constant factor approximation of the
  maximin problem.
- [`phragmms`]: Implements a hybrid approach inspired by Phragmén which is executed faster but
  it can achieve a constant factor approximation of the maximin problem, similar to that of the
  MMS algorithm.
- [`balance_solution`]: Implements the star balancing algorithm. This iterative process can push
  a solution toward being more `balances`, which in turn can increase its score.

### Terminology

This crate uses context-independent words, not to be confused with staking. This is because the
election algorithms of this crate, while designed for staking, can be used in other contexts as
well.

`Voter`: The entity casting some votes to a number of `Targets`. This is the same as `Nominator`
in the context of staking. `Target`: The entities eligible to be voted upon. This is the same as
`Validator` in the context of staking. `Edge`: A mapping from a `Voter` to a `Target`.

The goal of an election algorithm is to provide an `ElectionResult`. A data composed of:
- `winners`: A flat list of identifiers belonging to those who have won the election, usually
  ordered in some meaningful way. They are zipped with their total backing stake.
- `assignment`: A mapping from each voter to their winner-only targets, zipped with a ration
  denoting the amount of support given to that particular target.

```rust
// the winners.
let winners = vec![(1, 100), (2, 50)];
let assignments = vec![
    // A voter, giving equal backing to both 1 and 2.
    Assignment {
		who: 10,
		distribution: vec![(1, Perbill::from_percent(50)), (2, Perbill::from_percent(50))],
	},
    // A voter, Only backing 1.
    Assignment { who: 20, distribution: vec![(1, Perbill::from_percent(100))] },
];

// the combination of the two makes the election result.
let election_result = ElectionResult { winners, assignments };

```

The `Assignment` field of the election result is voter-major, i.e. it is from the perspective of
the voter. The struct that represents the opposite is called a `Support`. This struct is usually
accessed in a map-like manner, i.e. keyed vy voters, therefor it is stored as a mapping called
`SupportMap`.

Moreover, the support is built from absolute backing values, not ratios like the example above.
A struct similar to `Assignment` that has stake value instead of ratios is called an
`StakedAssignment`.


More information can be found at: https://arxiv.org/abs/2004.12990

License: Apache-2.0