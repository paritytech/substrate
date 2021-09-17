# Tipping Pallet ( pallet-tips )

**Note :: This pallet is tightly coupled to pallet-treasury**

A subsystem to allow for an agile "tipping" process, whereby a reward may be given without first
having a pre-determined stakeholder group come to consensus on how much should be paid.

A group of `Tippers` is determined through the config `Config`. After half of these have declared
some amount that they believe a particular reported reason deserves, then a countdown period is
entered where any remaining members can declare their tip amounts also. After the close of the
countdown period, the median of all declared tips is paid to the reported beneficiary, along with
any finders fee, in case of a public (and bonded) original report.

### Terminology

- **Tipping:** The process of gathering declarations of amounts to tip and taking the median amount
  to be transferred from the treasury to a beneficiary account.
- **Tip Reason:** The reason for a tip; generally a URL which embodies or explains why a particular
  individual (identified by an account ID) is worthy of a recognition by the treasury.
- **Finder:** The original public reporter of some reason for tipping.
- **Finders Fee:** Some proportion of the tip amount that is paid to the reporter of  the tip,
  rather than the main beneficiary.

## Interface

### Dispatchable Functions

- `report_awesome` - Report something worthy of a tip and register for a finders fee.
- `retract_tip` - Retract a previous (finders fee registered) report.
- `tip_new` - Report an item worthy of a tip and declare a specific amount to tip.
- `tip` - Declare or redeclare an amount to tip for a particular reason.
- `close_tip` - Close and pay out a tip.
- `slash_tip` - Remove and slash an already-open tip.