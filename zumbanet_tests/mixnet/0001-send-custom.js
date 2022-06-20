const { ApiPromise, WsProvider } = require('@polkadot/api');

async function connect(apiUrl, types) {
    const provider = new WsProvider(apiUrl);
		const api = await ApiPromise.create({
			provider,
			rpc: {
				author: {
					mixExtrinsic: {
						description: 'Send extrinsic to mixnet',
						params: [
							{
								name: 'payload',
								type: 'Vec<u8>' // should be 'Extrinsic', but test is an invalid extrinsic
							},
							{
								name: 'numberHop',
								type: 'u32'
							},
							{
								name: 'withSurb',
								type: 'Bool'
							}
						],
						type: 'Bool'
					}
				}
			}
		});
    await api.isReady;

    return api;
}

async function run(nodeName, networkInfo, args) {
    const {wsUri, userDefinedTypes} = networkInfo.nodesByName[nodeName];
    console.log(wsUri);
    console.log(userDefinedTypes);
    const api = await connect(wsUri, userDefinedTypes);
    const result = await api.rpc.author.mixExtrinsic(
			"0x5c0d1176a568c1f92944340dbfed9e9c530ebca703c85910e7164cb7d1c9e47b",
			3,
			false
		);
    console.log("bef calld");
    console.log(`${result}`);
//    return result;
    return 1;
}

module.exports = { run }
