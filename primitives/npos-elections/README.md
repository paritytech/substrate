A set of election algorithms to be used with a substrate runtime, typically within the staking
sub-system. Notable implementation include

- [`seq_phragmen`]: Implements the Phragmén Sequential Method. An un-ranked, relatively fast
  election method that ensures PJR, but does not provide a constant factor approximation of the
  maximin problem.
- [`balance_solution`]: Implements the star balancing algorithm. This iterative process can
  increase a solutions score, as described in [`evaluate_support`].

More information can be found at: https://arxiv.org/abs/2004.12990

License: Apache-2.0