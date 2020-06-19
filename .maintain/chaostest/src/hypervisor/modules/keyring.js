/**
 * Hypervisor module: function to manage private and public keys of all nodes
 */

const createPair = require('@polkadot/keyring/pair').default
// const { stringToU8a } = require('@polkadot/util')
const {
  cryptoWaitReady,
  naclKeypairFromSeed,
  schnorrkelKeypairFromSeed
} = require('@polkadot/util-crypto')

const Keyring = require('@polkadot/keyring').default;
const stringToU8a = require('@polkadot/util/string/toU8a').default;

async function main (str) {
  // Create account seed for Alice
  const ALICE_SEED = str.padEnd(32, ' ');
  console.log(ALICE_SEED, ALICE_SEED.length)

  // Create an instance of the Keyring
  const keyring = new Keyring();

  // Create pair and add Alice to keyring pair dictionary (with account seed)
  const pairAlice = keyring.addFromSeed(stringToU8a(ALICE_SEED));

  console.log(`Created keyring pair for Alice with address: ${keyring.getPair(pairAlice.address).address}`);
  console.log(pairAlice.toJson())
}
/**
 * @ignore
 */
const isSr25519 = (type) => type === 'sr25519';

/**
 * @ignore
 */
const fromSeed = (type, seed) =>
  isSr25519(type) ? schnorrkelKeypairFromSeed(seed) : naclKeypairFromSeed(seed);

/**
 * Create a {@link Keys} interface from a seed string
 * Note: only supports ed22519 for now
 */
const getKeysFromSeed = async (
  type,
  seed
) => {
  await cryptoWaitReady();
  const seedU8a = stringToU8a(seed.padEnd(32));
  const pair = fromSeed(type, seedU8a);
  const keyring = createPair(type, pair);

  return {
    address: keyring.address,
    seed: seedU8a,
    publicKey: keyring.publicKey,
    sign: keyring.sign
  };
}

const getNodeKeys = async (
  nodeId
) => {
  return {
    babe: await getKeysFromSeed(
      'sr25519',
      `${nodeId}/babe`
    ),
    controller: await getKeysFromSeed(
      'sr25519',
      `${nodeId}/controller`
    ),
    gran: await getKeysFromSeed(
      'ed25519',
      `${nodeId}/gran`
    ),
    imon: await getKeysFromSeed(
      'sr25519',
      `${nodeId}/imon`
    ),
    stash: await getKeysFromSeed(
      'sr25519',
      `${nodeId}/stash`
    )
  };
}

/**
 * Get the {@link Keys} of the sudo account
 */
const getSudoKeys = async () => {
  // sudo key is 'chaos'
  return getKeysFromSeed('ed25519', 'chaos');
}

module.exports = {getKeysFromSeed, getNodeKeys, getSudoKeys}
// main('node-validator-0')
const log = async () => {
    for (var i=0;i<51;i++) {
        const seed = `node-validator-${i}/gran`
        const key = await getKeysFromSeed('ed25519', seed)
        console.log('"'+key.address+'",')
    }
   
    // const keys2 = await getKeysFromSeed('ed25519', 'node-validator-1')
    // console.log(keys2.address)
};
log()