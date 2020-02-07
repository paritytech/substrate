//! # Internal types to ssync drain slog
//! FIXME: REMOVE THIS ONCE THE PR WAS MERGE
//! https://github.com/slog-rs/async/pull/14

use slog::{Record, RecordStatic, Level, SingleKV, KV, BorrowedKV};
use slog::{Serializer, OwnedKVList, Key};

use std::fmt;
use take_mut::take;

struct ToSendSerializer {
	kv: Box<dyn KV + Send>,
}

impl ToSendSerializer {
	fn new() -> Self {
		ToSendSerializer { kv: Box::new(()) }
	}

	fn finish(self) -> Box<dyn KV + Send> {
		self.kv
	}
}

impl Serializer for ToSendSerializer {
	fn emit_bool(&mut self, key: Key, val: bool) -> slog::Result {
		take(&mut self.kv, |kv| Box::new((kv, SingleKV(key, val))));
		Ok(())
	}
	fn emit_unit(&mut self, key: Key) -> slog::Result {
		take(&mut self.kv, |kv| Box::new((kv, SingleKV(key, ()))));
		Ok(())
	}
	fn emit_none(&mut self, key: Key) -> slog::Result {
		let val: Option<()> = None;
		take(&mut self.kv, |kv| Box::new((kv, SingleKV(key, val))));
		Ok(())
	}
	fn emit_char(&mut self, key: Key, val: char) -> slog::Result {
		take(&mut self.kv, |kv| Box::new((kv, SingleKV(key, val))));
		Ok(())
	}
	fn emit_u8(&mut self, key: Key, val: u8) -> slog::Result {
		take(&mut self.kv, |kv| Box::new((kv, SingleKV(key, val))));
		Ok(())
	}
	fn emit_i8(&mut self, key: Key, val: i8) -> slog::Result {
		take(&mut self.kv, |kv| Box::new((kv, SingleKV(key, val))));
		Ok(())
	}
	fn emit_u16(&mut self, key: Key, val: u16) -> slog::Result {
		take(&mut self.kv, |kv| Box::new((kv, SingleKV(key, val))));
		Ok(())
	}
	fn emit_i16(&mut self, key: Key, val: i16) -> slog::Result {
		take(&mut self.kv, |kv| Box::new((kv, SingleKV(key, val))));
		Ok(())
	}
	fn emit_u32(&mut self, key: Key, val: u32) -> slog::Result {
		take(&mut self.kv, |kv| Box::new((kv, SingleKV(key, val))));
		Ok(())
	}
	fn emit_i32(&mut self, key: Key, val: i32) -> slog::Result {
		take(&mut self.kv, |kv| Box::new((kv, SingleKV(key, val))));
		Ok(())
	}
	fn emit_f32(&mut self, key: Key, val: f32) -> slog::Result {
		take(&mut self.kv, |kv| Box::new((kv, SingleKV(key, val))));
		Ok(())
	}
	fn emit_u64(&mut self, key: Key, val: u64) -> slog::Result {
		take(&mut self.kv, |kv| Box::new((kv, SingleKV(key, val))));
		Ok(())
	}
	fn emit_i64(&mut self, key: Key, val: i64) -> slog::Result {
		take(&mut self.kv, |kv| Box::new((kv, SingleKV(key, val))));
		Ok(())
	}
	fn emit_f64(&mut self, key: Key, val: f64) -> slog::Result {
		take(&mut self.kv, |kv| Box::new((kv, SingleKV(key, val))));
		Ok(())
	}
	fn emit_usize(&mut self, key: Key, val: usize) -> slog::Result {
		take(&mut self.kv, |kv| Box::new((kv, SingleKV(key, val))));
		Ok(())
	}
	fn emit_isize(&mut self, key: Key, val: isize) -> slog::Result {
		take(&mut self.kv, |kv| Box::new((kv, SingleKV(key, val))));
		Ok(())
	}
	fn emit_str(&mut self, key: Key, val: &str) -> slog::Result {
		let val = val.to_owned();
		take(&mut self.kv, |kv| Box::new((kv, SingleKV(key, val))));
		Ok(())
	}
	fn emit_arguments(
		&mut self,
		key: Key,
		val: &fmt::Arguments,
	) -> slog::Result {
		let val = fmt::format(*val);
		take(&mut self.kv, |kv| Box::new((kv, SingleKV(key, val))));
		Ok(())
	}

	fn emit_serde(&mut self, key: Key, value: &dyn slog::SerdeValue) -> slog::Result {
		let val = value.to_sendable();
		take(&mut self.kv, |kv| Box::new((kv, SingleKV(key, val))));
		Ok(())
	}
}

pub(crate) struct AsyncRecord {
	msg: String,
	level: Level,
	location: Box<slog::RecordLocation>,
	tag: String,
	logger_values: OwnedKVList,
	kv: Box<dyn KV + Send>,
}

impl AsyncRecord {
	/// Serializes a `Record` and an `OwnedKVList`.
	pub fn from(record: &Record, logger_values: &OwnedKVList) -> Self {
		let mut ser = ToSendSerializer::new();
		record
			.kv()
			.serialize(record, &mut ser)
			.expect("`ToSendSerializer` can't fail");

		AsyncRecord {
			msg: fmt::format(*record.msg()),
			level: record.level(),
			location: Box::new(*record.location()),
			tag: String::from(record.tag()),
			logger_values: logger_values.clone(),
			kv: ser.finish(),
		}
	}

	/// Deconstruct this `AsyncRecord` into a record and `OwnedKVList`.
	pub fn as_record_values(&self, mut f: impl FnMut(&Record, &OwnedKVList)) {
		let rs = RecordStatic {
			location: &*self.location,
			level: self.level,
			tag: &self.tag,
		};

		f(&Record::new(
			&rs,
			&format_args!("{}", self.msg),
			BorrowedKV(&self.kv),
		), &self.logger_values)
	}
}
