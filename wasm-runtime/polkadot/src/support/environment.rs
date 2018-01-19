use runtime_support::{Rc, RefCell, transmute, Box};
use primitives::{BlockNumber, Digest};

#[derive(Default)]
pub struct Environment {
	pub block_number: BlockNumber,
	pub digest: Digest,
	pub next_log_index: usize,
}

pub fn with_env<T, F: FnOnce(&mut Environment) -> T>(f: F) -> T {
	let e = env();
	let mut eb = e.borrow_mut();
	f(&mut *eb)
}

#[cfg(not(test))]
pub fn env() -> Rc<RefCell<Environment>> {
	// Initialize it to a null value
	static mut SINGLETON: *const Rc<RefCell<Environment>> = 0 as *const Rc<RefCell<Environment>>;

	unsafe {
		if SINGLETON == 0 as *const Rc<RefCell<Environment>> {
			// Make it
			let singleton: Rc<RefCell<Environment>> = Rc::new(RefCell::new(Default::default()));

			// Put it in the heap so it can outlive this call
			SINGLETON = transmute(Box::new(singleton));
		}

		// Now we give out a copy of the data that is safe to use concurrently.
		(*SINGLETON).clone()
	}
}

#[cfg(test)]
pub fn env() -> Rc<RefCell<Environment>> {
	// Initialize it to a null value
	thread_local!{
		static SINGLETON: RefCell<*const Rc<RefCell<Environment>>> = RefCell::new(0 as *const Rc<RefCell<Environment>>);
	}

	SINGLETON.with(|s| unsafe {
		if *s.borrow() == 0 as *const Rc<RefCell<Environment>> {
			// Make it
			let singleton: Rc<RefCell<Environment>> = Rc::new(RefCell::new(Default::default()));

			// Put it in the heap so it can outlive this call
			*s.borrow_mut() = transmute(Box::new(singleton));
		}

		// Now we give out a copy of the data that is safe to use concurrently.
		(**s.borrow()).clone()
	})
}
