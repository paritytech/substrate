`default_genesis_config.json` file was written with the following code:
```
	use crate::genesismap::GenesisStorageBuilder;
	#[test]
	fn write_default_config_to_tmp_file() {
		let j = json::to_string(&GenesisStorageBuilder::default().genesis_config()).unwrap().into_bytes();
		let mut file = fs::OpenOptions::new()
			.create(true)
			.write(true)
			.open("/tmp/default_genesis_config.json").unwrap();
		file.write_all(&j);
	}
```

`:code` field was manually truncated to reduce file size. Test is only comparing keys, not the values.
