use std::fmt;

#[derive(Debug, Clone)]
pub struct KeySpecs {
	pub desired_pattern: String,
	pub case_sensitive: bool,
	pub minscore: f32,
}

impl fmt::Display for KeySpecs {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, r#"Key specifications:
 - Pattern:        {}
 - Case sensitive: {}
 - Min. Score:     {}"#,
        	self.desired_pattern,
        	self.case_sensitive,
        	self.minscore)
    }
}
