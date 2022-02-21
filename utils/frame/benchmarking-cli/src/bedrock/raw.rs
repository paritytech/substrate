/*



/// Raw DB read performance of the underlying Database.
/// Does not represent a Read from in Substrate, since they funnel through a Trie first.
pub fn raw_db_read(cfg: &BedrockParams, db: DB) {

}



/*fn child_keys<B, BA, C>(block: BlockId<B>, client: Arc<C>) -> Result<Vec<(ChildInfo, StorageKey)>>
where
	C: UsageProvider<B> + StorageProvider<B, BA>,
	B: BlockT,
	BA: Backend<B>,
{
	let empty_key = StorageKey(Vec::new());
	let mut top_keys = client.storage_keys(&block, &empty_key)?;
	let mut child_keys = Vec::<(ChildInfo, StorageKey)>::new();

	// Loop through all top keys and find their respective child keys, if any.
	while let Some(pos) = top_keys
		.iter()
		.position(|k| k.0.starts_with(well_known_keys::DEFAULT_CHILD_STORAGE_KEY_PREFIX))
	{
		let key = top_keys.swap_remove(pos);

		let key =
			StorageKey(key.0[well_known_keys::DEFAULT_CHILD_STORAGE_KEY_PREFIX.len()..].to_vec());
		let child_info = ChildInfo::new_default(&key.0);

		let keys = client.child_storage_keys(&block, &child_info, &empty_key)?;
		keys.into_iter().for_each(|k| {
			child_keys.push((child_info.clone(), k));
		});
	}

	Ok(child_keys)
}*/

*/
