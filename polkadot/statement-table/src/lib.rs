// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! The statement table.
//!
//! This stores messages other authorities issue about candidates.
//!
//! These messages are used to create a proposal submitted to a BFT consensus process.
//!
//! Proposals are formed of sets of candidates which have the requisite number of
//! validity and availability votes.
//!
//! Each parachain is associated with two sets of authorities: those which can
//! propose and attest to validity of candidates, and those who can only attest
//! to availability.

extern crate substrate_codec as codec;
extern crate substrate_primitives;
extern crate polkadot_primitives as primitives;

#[macro_use]
extern crate substrate_codec_derive;

pub mod generic;

pub use generic::Table;

use primitives::parachain::{Id, CandidateReceipt, CandidateSignature as Signature};
use primitives::{SessionKey, Hash};

/// Statements about candidates on the network.
pub type Statement = generic::Statement<CandidateReceipt, Hash>;

/// Signed statements about candidates.
pub type SignedStatement = generic::SignedStatement<CandidateReceipt, Hash, SessionKey, Signature>;

/// Kinds of misbehavior, along with proof.
pub type Misbehavior = generic::Misbehavior<CandidateReceipt, Hash, SessionKey, Signature>;

/// A summary of import of a statement.
pub type Summary = generic::Summary<Hash, Id>;

/// Context necessary to construct a table.
pub trait Context {
	/// Whether a authority is a member of a group.
	/// Members are meant to submit candidates and vote on validity.
	fn is_member_of(&self, authority: &SessionKey, group: &Id) -> bool;

	/// Whether a authority is an availability guarantor of a group.
	/// Guarantors are meant to vote on availability for candidates submitted
	/// in a group.
	fn is_availability_guarantor_of(
		&self,
		authority: &SessionKey,
		group: &Id,
	) -> bool;

	// requisite number of votes for validity and availability respectively from a group.
	fn requisite_votes(&self, group: &Id) -> (usize, usize);
}

impl<C: Context> generic::Context for C {
	type AuthorityId = SessionKey;
	type Digest = Hash;
	type GroupId = Id;
	type Signature = Signature;
	type Candidate = CandidateReceipt;

	fn candidate_digest(candidate: &CandidateReceipt) -> Hash {
		candidate.hash()
	}

	fn candidate_group(candidate: &CandidateReceipt) -> Id {
		candidate.parachain_index.clone()
	}

	fn is_member_of(&self, authority: &SessionKey, group: &Id) -> bool {
		Context::is_member_of(self, authority, group)
	}

	fn is_availability_guarantor_of(&self, authority: &SessionKey, group: &Id) -> bool {
		Context::is_availability_guarantor_of(self, authority, group)
	}

	fn requisite_votes(&self, group: &Id) -> (usize, usize) {
		Context::requisite_votes(self, group)
	}
}
