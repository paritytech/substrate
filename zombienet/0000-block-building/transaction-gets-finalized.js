//based on: https://polkadot.js.org/docs/api/examples/promise/transfer-events

const assert = require("assert");

async function run(nodeName, networkInfo, args) {
  const {wsUri, userDefinedTypes} = networkInfo.nodesByName[nodeName];
  const api = await zombie.connect(wsUri, userDefinedTypes);

  // Construct the keyring after the API (crypto has an async init)
  const keyring = new zombie.Keyring({ type: "sr25519" });

  // Add Alice to our keyring with a hard-derivation path (empty phrase, so uses dev)
  const alice = keyring.addFromUri('//Alice');
  const bob = '5FHneW46xGXgs5mUiveU4sbTyGBzmstUspZC92UhjJM694ty';

  // Create a extrinsic, transferring 10^20 units to Bob
  const transfer = api.tx.balances.transferAllowDeath(bob, 10n**20n);

  let transaction_success_event = false;
  try {
    await new Promise( async (resolve, reject) => {
      const unsubscribe = await transfer
        .signAndSend(alice, { nonce: -1 }, ({ events = [], status }) => {
          console.log('Transaction status:', status.type);

          if (status.isInBlock) {
            console.log('Included at block hash', status.asInBlock.toHex());
            console.log('Events:');

            events.forEach(({ event: { data, method, section }, phase }) => {
              console.log('\t', phase.toString(), `: ${section}.${method}`, data.toString());

              if (section=="system" && method =="ExtrinsicSuccess") {
                transaction_success_event = true;
              }
            });
          } else if (status.isFinalized) {
            console.log('Finalized block hash', status.asFinalized.toHex());
            unsubscribe();
            if (transaction_success_event) {
              resolve();
            } else {
              reject("ExtrinsicSuccess has not been seen");
            }
          } else if (status.isError) {
            unsubscribe();
            reject("Transaction status.isError");
          }

        });
    });
  } catch (error) {
    assert.fail("Transfer promise failed, error: " + error);
  }

  assert.ok("test passed");
}

module.exports = { run }
