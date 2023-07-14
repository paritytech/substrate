# Pallet Broker

Brokerage tool for managing Polkadot Core scheduling.

Properly described in RFC-0001 Agile Coretime.

## Implemnentation Specifics

### The Sale

```nocompile
					1 1 1 1 1 1 1 1 1 1 2 2 2 2 2 2 2 2
0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7
--------------------------------------------------------
< interlude  >
			  <                   sale                 >
							... of which ...
			  <  descending-price   ><   fixed-price   >
														| <-------\
price fixed, unsold assigned to instapool, system cores reserved -/
```

## TODO

- More Events

- Benchmarks
- Weights
- Final docs
- Tests
  - Tests for dropping out of date storage
  - Tests for core count changes
  - Tests for every error
