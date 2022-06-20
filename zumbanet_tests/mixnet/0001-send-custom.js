const { ApiPromise, WsProvider } = require('@polkadot/api');

async function connect(apiUrl, types) {
    const provider = new WsProvider(apiUrl);
    const api = new ApiPromise({ provider, types });
    await api.isReady;
		await ApiPromise.create({
			rpc: {
				author: {
					mixExtrinsic: {
						description: 'Send extrinsic to mixnet',
						params: [
							{
								name: 'payload',
								type: 'Extrinsic'
							},
							{
								name: 'numberHop',
								type: 'integer'
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

    return api;
}

async function run(nodeName, networkInfo, args) {
    const {wsUri, userDefinedTypes} = networkInfo.nodesByName[nodeName];
    const api = await connect(wsUri, userDefinedTypes);
    console.log("bef call");
    const result = await api.rpc.author.mixExtrinsic(
			"0x5c0d1176a568c1f92944340dbfed9e9c530ebca703c85910e7164cb7d1c9e47b",
			3,
			false
		);
    console.log(`${result}`);
//    return result;
    return 1;
}

module.exports = { run }
