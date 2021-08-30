# Keys and Security

The following information is not exhaustive but meant to prevent the most common mistakes.
You can read more about security and risks in the [Polkadot Wiki](https://wiki.polkadot.network/docs/learn-account-generation).
The Polkadot network has a few **test networks**, e.g. **Westend**. Test networks are a great way to experiment and learn safely as you can lose tokens on those networks without any financial consequences.

`subkey` generates and provides 2 pieces of **secret** information:
- **secret phrase**: a bunch of words, exactly 12 by default (can be 12, 15, 18, 21 or 24)
- **secret seed**: a big hexadecimal value

There are 2 risks related to private keys:
- loss of keys: this can happen if you don't have a proper backup
- leak of the keys: this can unfortunately happen in many ways, including malware, phishing, key logger, backups on system that are online and not properly secured

You want to ensure that:
- you **do not lose** those secrets
- **no one but you can access** those secrets

☠️ **DO NOT SHARE** your mnemonic phrase or secret seed with ANYONE under **ANY** circumstances. Doing so would give them access to your funds and to send transactions on your behalf.

☠️ If someone is asking for your **secret** phrase or **secret** seed, you can be **SURE** they are attempting to steal your funds.

✅ It is however fine to share your **SS58 Address** as this is meant to be public information and is needed by anyone you want to be able to make transfer to or otherwise interact with your account. They will only ever need your **Public Address**.

⚠️ While using the same key on multiple networks is possible, it is usually **not** recommended unless you have good motivations for doing so and understand the associated risks and drawbacks.
