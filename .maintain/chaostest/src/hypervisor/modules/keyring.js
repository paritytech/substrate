/**
 * Hypervisor module: function to manage private and public keys of all nodes
 */

const createPair = require('@polkadot/keyring/pair').default
const {
  cryptoWaitReady,
  naclKeypairFromSeed,
  schnorrkelKeypairFromSeed
} = require('@polkadot/util-crypto')
const { u8aToHex } = require('@polkadot/util')
const stringToU8a = require('@polkadot/util/string/toU8a').default;

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
  // Using current dev/local sudo key
    return '5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY'
}

const getKeyFromNodeId = (nodeId) => {
    const u8a = stringToU8a(nodeId.padEnd(32))
    return u8aToHex(u8a, undefined, false) // remove 0x in front
}

module.exports = {getKeysFromSeed, getNodeKeys, getSudoKeys, getKeyFromNodeId}